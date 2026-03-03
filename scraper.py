# ==========================================================
# KIND(메인) + DART(같은 보고서일 때만 우선 덮기) 통합
# - 매번 실행할 때마다 업데이트(덮어쓰기) 가능: SKIP_SEEN=false 권장
# - KIND로 1차 레코드 생성
# - DART가 "같은 보고서"로 판정되면 핵심 8개 컬럼을 DART로 덮어씀
#   핵심: 신규발행주식수, 증자전 주식수, 증자비율, 자금용도, 확정발행금액(억원),
#        확정발행가(원), 기준주가, 할인(할증률)
# ==========================================================

import os
import re
import json
import time
import io
import zipfile
from dataclasses import dataclass
from datetime import datetime, timedelta
from pathlib import Path
from typing import List, Optional, Tuple, Set, Dict

import feedparser
import pandas as pd
from bs4 import BeautifulSoup
import gspread
from gspread.utils import rowcol_to_a1
from playwright.sync_api import sync_playwright
import requests

# ==========================================================
# Config (ENV)
# ==========================================================
BASE = "https://kind.krx.co.kr"
DEFAULT_RSS = (
    "http://kind.krx.co.kr:80/disclosure/rsstodaydistribute.do"
    "?method=searchRssTodayDistribute&mktTpCd=0&currentPageSize=100"
)

RSS_URL = os.getenv("RSS_URL", DEFAULT_RSS)
KEYWORDS = [x.strip() for x in os.getenv("KEYWORDS", "유상증자").split(",") if x.strip()]

HEADLESS = os.getenv("HEADLESS", "true").lower() == "true"
LIMIT = int(os.getenv("LIMIT", "30"))
RUN_ONE_ACPTNO = os.getenv("RUN_ONE_ACPTNO", "").strip()

# ✅ 핵심: 기본 false(=스킵 안 함, 매번 업데이트)
SKIP_SEEN = os.getenv("SKIP_SEEN", "false").lower() == "true"

GOOGLE_SHEET_ID = os.environ.get("GOOGLE_SHEET_ID", "").strip()
GOOGLE_CREDENTIALS_JSON = (
    os.environ.get("GOOGLE_CREDENTIALS_JSON", "").strip()
    or os.environ.get("GOOGLE_CREDS", "").strip()
)

RIGHTS_OUT_SHEET = os.getenv("RIGHTS_OUT_SHEET", "유상증자")
SEEN_SHEET_NAME = os.getenv("SEEN_SHEET_NAME", "seen")

# DART
DART_API_KEY = os.getenv("DART_API_KEY", "").strip()
DART_LOOKBACK_DAYS = int(os.getenv("DART_LOOKBACK_DAYS", "30"))
DART_TIMEOUT = int(os.getenv("DART_TIMEOUT", "20"))
SAME_REPORT_MAX_DAYS = int(os.getenv("SAME_REPORT_MAX_DAYS", "5"))

# Debug
OUTDIR = Path(os.getenv("OUTDIR", "out"))
DEBUGDIR = OUTDIR / "debug"

# ✅ 네 기존 컬럼 그대로
RIGHTS_COLUMNS = [
    "회사명", "상장시장", "최초 이사회결의일", "증자방식", "발행상품", "신규발행주식수",
    "확정발행가(원)", "기준주가", "확정발행금액(억원)", "할인(할증률)",
    "증자전 주식수", "증자비율", "납입일", "신주의 배당기산일", "신주의 상장 예정일",
    "이사회결의일", "자금용도", "투자자", "링크", "접수번호"
]

@dataclass
class Target:
    acpt_no: str
    title: str
    link: str

# ==========================================================
# Utils
# ==========================================================
def _norm(s: str) -> str:
    s = (s or "").strip()
    s = re.sub(r"\s+", "", s)
    s = s.replace(":", "")
    return s

def _norm_date(s: str) -> str:
    return re.sub(r"[^\d]", "", (s or "").strip())

def _to_int(s: str) -> Optional[int]:
    if s is None:
        return None
    t = str(s).replace(",", "")
    t = re.sub(r"[^\d\-]", "", t)
    if t in ("", "-"):
        return None
    try:
        return int(t)
    except:
        return None

def _to_float(s: str) -> Optional[float]:
    if s is None:
        return None
    t = str(s).replace(",", "")
    t = re.sub(r"[^\d\.\-]", "", t)
    if t in ("", "-", "."):
        return None
    try:
        return float(t)
    except:
        return None

def _max_int_in_text(s: str) -> Optional[int]:
    if not s:
        return None
    nums = re.findall(r"\d[\d,]*", str(s))
    vals = []
    for x in nums:
        v = _to_int(x)
        if v is not None:
            vals.append(v)
    return max(vals) if vals else None

def extract_acpt_no(text: str) -> Optional[str]:
    m = re.search(r"acptNo=(\d{14})", text or "")
    return m.group(1) if m else None

def company_from_title(title: str) -> str:
    m = re.search(r"\[([^\]]+)\]", title or "")
    return m.group(1).strip() if m else ""

def market_from_title(title: str) -> str:
    if not title:
        return ""
    if "[코]" in title:
        return "코스닥"
    if "[유]" in title:
        return "유가증권"
    if "[넥]" in title or "[코넥]" in title:
        return "코넥스"
    return ""

def viewer_url(acpt_no: str, docno: str = "") -> str:
    return f"{BASE}/common/disclsviewer.do?method=searchInitInfo&acptNo={acpt_no}&docno={docno}"

def match_keyword(title: str) -> bool:
    return bool(title) and any(k in title for k in KEYWORDS)

def is_correction_title(title: str) -> bool:
    """제목 '맨 앞'이 정정인 경우만"""
    return bool(title) and title.strip().startswith("정정")

def make_event_key(company: str, first_board_date: str, method: str) -> str:
    return f"{_norm(company)}|{_norm_date(first_board_date)}|{_norm(method)}"

def _safe_dt_yyyymmdd(s: str) -> Optional[datetime]:
    s2 = _norm_date(s)
    if len(s2) != 8:
        return None
    try:
        return datetime.strptime(s2, "%Y%m%d")
    except:
        return None

def _norm_company(name: str) -> str:
    s = (name or "").strip()
    s = re.sub(r"\(주\)|주식회사|㈜", "", s)
    s = re.sub(r"\s+", "", s)
    s = re.sub(r"[^\w가-힣]", "", s)
    return s

def _fmt_int(n: int) -> str:
    return f"{n:,}"

def _fmt_amt_uk(n_won: int) -> str:
    return f"{(n_won / 100_000_000):,.2f}"

# ==========================================================
# RSS → targets
# ==========================================================
def parse_rss_targets() -> List[Target]:
    feed = feedparser.parse(RSS_URL)
    items = feed.entries or []
    targets: List[Target] = []

    for it in items:
        title = getattr(it, "title", "") or ""
        link = getattr(it, "link", "") or ""
        guid = getattr(it, "guid", "") or ""

        if not match_keyword(title):
            continue

        acpt_no = extract_acpt_no(link) or extract_acpt_no(guid)
        if not acpt_no:
            continue

        targets.append(Target(acpt_no=acpt_no, title=title, link=link))

    uniq = {}
    for t in targets:
        uniq.setdefault(t.acpt_no, t)
    return list(uniq.values())

# ==========================================================
# Playwright: popup html → dfs
# ==========================================================
def is_block_page(html: str) -> bool:
    if not html:
        return True
    lower = html.lower()
    suspects = ["비정상", "접근", "제한", "차단", "오류", "error", "권한", "잠시 후", "관리자"]
    return any(s in lower for s in suspects) and ("<table" not in lower)

def frame_score(html: str) -> int:
    if not html:
        return -1
    lower = html.lower()
    tcnt = lower.count("<table")
    if tcnt == 0:
        return -1
    bonus_words = ["기준주가", "납입", "이사회", "할인", "할증", "발행", "청약", "증자방식", "자금조달", "정정사항"]
    bonus = sum(1 for w in bonus_words if w in lower)
    length_bonus = min(len(lower) // 2000, 50)
    return tcnt * 100 + bonus * 30 + length_bonus

def pick_best_frame_html(page) -> str:
    best_html, best_score = "", -1
    for fr in page.frames:
        try:
            html = fr.content()
            sc = frame_score(html)
            if sc > best_score:
                best_score = sc
                best_html = html
        except Exception:
            continue
    return best_html

def extract_tables_from_html_robust(html: str) -> List[pd.DataFrame]:
    html = (html or "").replace("\x00", "")

    try:
        dfs = pd.read_html(html, header=None)
        return [df.where(pd.notnull(df), "") for df in dfs]
    except Exception:
        pass

    soup = BeautifulSoup(html, "lxml")
    for tag in soup(["script", "style", "noscript"]):
        tag.decompose()

    tables = soup.find_all("table")
    results: List[pd.DataFrame] = []

    for tbl in tables:
        try:
            one = pd.read_html(str(tbl), header=None)
            if one:
                results.append(one[0].where(pd.notnull(one[0]), ""))
                continue
        except Exception:
            pass

        rows = []
        for tr in tbl.find_all("tr"):
            cells = tr.find_all(["th", "td"])
            row = [c.get_text(" ", strip=True) for c in cells]
            if row:
                rows.append(row)

        if rows:
            max_len = max(len(r) for r in rows)
            normed = [r + [""] * (max_len - len(r)) for r in rows]
            results.append(pd.DataFrame(normed))

    if not results:
        raise ValueError("No tables parsed (robust).")

    return results

def save_debug(acpt_no: str, page, html: str, reason: str):
    try:
        OUTDIR.mkdir(parents=True, exist_ok=True)
        DEBUGDIR.mkdir(parents=True, exist_ok=True)
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        (DEBUGDIR / f"{acpt_no}_{ts}_{reason}.html").write_text(html or "", encoding="utf-8")
        try:
            page.screenshot(path=str(DEBUGDIR / f"{acpt_no}_{ts}_{reason}.png"), full_page=True)
        except Exception:
            pass
    except Exception:
        pass

def scrape_one(context, t: Target) -> Tuple[List[pd.DataFrame], str]:
    url = viewer_url(t.acpt_no)
    page = context.new_page()
    try:
        page.goto(url, wait_until="networkidle", timeout=60000)
        page.wait_for_timeout(1500)

        html = pick_best_frame_html(page) or ""
        if is_block_page(html) or html.lower().count("<table") == 0:
            save_debug(t.acpt_no, page, page.content(), "block_or_table0")
            raise RuntimeError("차단/오류/프레임 문제로 table을 못 찾음")

        dfs = extract_tables_from_html_robust(html)
        return dfs, url
    finally:
        try:
            page.close()
        except Exception:
            pass

# ==========================================================
# Google Sheets
# ==========================================================
def gs_open():
    if not GOOGLE_SHEET_ID or not GOOGLE_CREDENTIALS_JSON:
        raise RuntimeError("GOOGLE_SHEET_ID / GOOGLE_CREDS 가 비어있습니다. Secrets 확인")

    creds = json.loads(GOOGLE_CREDENTIALS_JSON)
    gc = gspread.service_account_from_dict(creds)
    sh = gc.open_by_key(GOOGLE_SHEET_ID)

    try:
        seen_ws = sh.worksheet(SEEN_SHEET_NAME)
    except gspread.WorksheetNotFound:
        seen_ws = sh.add_worksheet(title=SEEN_SHEET_NAME, rows=5000, cols=2)
        seen_ws.update("A1:B1", [["acptNo", "ts"]])

    try:
        rights_ws = sh.worksheet(RIGHTS_OUT_SHEET)
    except gspread.WorksheetNotFound:
        rights_ws = sh.add_worksheet(title=RIGHTS_OUT_SHEET, rows=5000, cols=len(RIGHTS_COLUMNS) + 5)

    return sh, rights_ws, seen_ws

def ensure_headers(ws, headers: List[str]):
    cur = ws.row_values(1)
    if cur != headers:
        end = rowcol_to_a1(1, len(headers))
        ws.update(f"A1:{end}", [headers])

def load_sheet_values(ws, headers: List[str]) -> List[List[str]]:
    ensure_headers(ws, headers)
    vals = ws.get_all_values()
    if not vals:
        end = rowcol_to_a1(1, len(headers))
        ws.update(f"A1:{end}", [headers])
        vals = ws.get_all_values()
    return vals

def build_acpt_index_from_values(values: List[List[str]], headers: List[str], key_field: str) -> Dict[str, int]:
    key_col = headers.index(key_field)
    idx: Dict[str, int] = {}
    for r, row in enumerate(values[1:], start=2):
        key = (row[key_col] if key_col < len(row) else "").strip()
        if key.isdigit():
            idx[key] = r
    return idx

def build_event_index_from_values(values: List[List[str]], headers: List[str]) -> Dict[str, Tuple[int, str]]:
    col_company = headers.index("회사명")
    col_first = headers.index("최초 이사회결의일")
    col_method = headers.index("증자방식")
    col_acpt = headers.index("접수번호")

    idx: Dict[str, Tuple[int, str]] = {}
    for r, row in enumerate(values[1:], start=2):
        company = (row[col_company] if col_company < len(row) else "").strip()
        first = (row[col_first] if col_first < len(row) else "").strip()
        method = (row[col_method] if col_method < len(row) else "").strip()
        acpt = (row[col_acpt] if col_acpt < len(row) else "").strip()

        k = make_event_key(company, first, method)
        if k.strip("|") and k not in idx:
            idx[k] = (r, acpt)
    return idx

def update_row(ws, headers: List[str], row: int, record: dict):
    ensure_headers(ws, headers)
    row_vals = [record.get(h, "") for h in headers]
    end = rowcol_to_a1(row, len(headers))
    ws.update(f"A{row}:{end}", [row_vals])

def upsert(ws, headers: List[str], index: Dict[str, int], record: dict, key_field: str, last_row_ref: Optional[List[int]] = None) -> Tuple[str, int]:
    ensure_headers(ws, headers)
    key = str(record.get(key_field, "")).strip()
    row_vals = [record.get(h, "") for h in headers]

    if key in index:
        r = index[key]
        end = rowcol_to_a1(r, len(headers))
        ws.update(f"A{r}:{end}", [row_vals])
        return "update", r

    ws.append_row(row_vals, value_input_option="RAW")
    if last_row_ref is not None:
        last_row_ref[0] += 1
        r = last_row_ref[0]
    else:
        r = len(ws.get_all_values())
    index[key] = r
    return "append", r

def load_seen_map(seen_ws) -> Dict[str, int]:
    vals = seen_ws.get_all_values()
    if not vals or len(vals) < 2:
        return {}
    m = {}
    for i, row in enumerate(vals[1:], start=2):
        k = (row[0] if len(row) > 0 else "").strip()
        if k.isdigit():
            m[k] = i
    return m

def upsert_seen(seen_ws, seen_map: Dict[str, int], acpt_no: str):
    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    if acpt_no in seen_map:
        r = seen_map[acpt_no]
        seen_ws.update(f"B{r}", [[ts]])
    else:
        seen_ws.append_row([acpt_no, ts], value_input_option="RAW")
        seen_map[acpt_no] = len(seen_ws.get_all_values())

# ==========================================================
# KIND Parser helpers
# ==========================================================
def scan_label_value(dfs: List[pd.DataFrame], label_candidates: List[str]) -> str:
    cand = {_norm(x) for x in label_candidates}

    for df in dfs:
        arr = df.astype(str).values
        R, C = arr.shape

        for r in range(R):
            for c in range(C):
                cell = _norm(arr[r][c])
                if cell in cand:
                    checks = []
                    for rr, cc in [(r, c+1), (r, c+2), (r+1, c), (r+1, c+1)]:
                        if 0 <= rr < R and 0 <= cc < C:
                            v = str(arr[rr][cc]).strip()
                            if v and v.lower() != "nan":
                                checks.append(v)

                    row_vals = [str(x).strip() for x in arr[r].tolist()
                                if str(x).strip() and str(x).strip().lower() != "nan"]
                    row_vals = [x for x in row_vals if _norm(x) not in cand]

                    for v in checks + row_vals:
                        if re.fullmatch(r"\d+\.", v):
                            continue
                        return v
    return ""

def find_row_best_int(dfs: List[pd.DataFrame], must_contain: List[str]) -> Optional[int]:
    keys = [_norm(x) for x in must_contain]
    best = None

    for df in dfs:
        arr = df.astype(str).values
        for r in range(arr.shape[0]):
            row = [str(x).strip() for x in arr[r].tolist()]
            joined = _norm("".join(row))
            if all(k in joined for k in keys):
                nums = [_to_int(x) for x in row]
                nums = [x for x in nums if x is not None and x > 0]
                if nums:
                    m = max(nums)
                    if best is None or m > best:
                        best = m
    return best

def find_row_best_float(dfs: List[pd.DataFrame], must_contain: List[str]) -> Optional[float]:
    keys = [_norm(x) for x in must_contain]
    for df in dfs:
        arr = df.astype(str).values
        for r in range(arr.shape[0]):
            row = [str(x).strip() for x in arr[r].tolist()]
            joined = _norm("".join(row))
            if all(k in joined for k in keys):
                vals = [_to_float(x) for x in row]
                vals = [x for x in vals if x is not None]
                if vals:
                    return max(vals, key=lambda z: abs(z))
    return None

def build_fund_use_text(dfs: List[pd.DataFrame]) -> str:
    keys = ["시설자금", "영업양수자금", "운영자금", "채무상환자금", "타법인증권취득자금", "타법인증권", "기타자금"]
    parts = []
    for k in keys:
        best = None
        for df in dfs:
            arr = df.astype(str).values
            for r in range(arr.shape[0]):
                row = [str(x).strip() for x in arr[r].tolist()]
                if _norm(k) in _norm("".join(row)):
                    nums = [_to_int(x) for x in row]
                    nums = [x for x in nums if x is not None and x >= 1_000_000]
                    if nums:
                        m = max(nums)
                        if best is None or m > best:
                            best = m
        if best is not None:
            parts.append(f"{k}:{best:,}")
    return "; ".join(parts)

def extract_investors(dfs: List[pd.DataFrame], corr_after: Optional[Dict[str, str]] = None) -> str:
    v = scan_label_value_preferring_correction(
        dfs,
        ["제3자배정대상자", "제3자배정 대상자", "대표주관사/투자자", "투자자"],
        corr_after=corr_after
    )
    return v or ""

def extract_correction_after_map(dfs: List[pd.DataFrame]) -> Dict[str, str]:
    out: Dict[str, str] = {}

    for df in dfs:
        try:
            arr = df.astype(str).values
        except Exception:
            continue

        R, C = arr.shape
        header_r = None
        after_col = None
        item_col = None

        for r in range(R):
            row_norm = [_norm(x) for x in arr[r].tolist()]
            has_before = any("정정전" in x for x in row_norm)
            has_after = any("정정후" in x for x in row_norm)
            if has_before and has_after:
                header_r = r
                after_col = next((i for i, x in enumerate(row_norm) if "정정후" in x), None)
                item_col = next(
                    (i for i, x in enumerate(row_norm) if ("정정사항" in x or "정정항목" in x or x == "항목")),
                    0
                )
                break

        if header_r is None or after_col is None:
            continue

        last_item = ""
        for rr in range(header_r + 1, R):
            item = str(arr[rr][item_col]).strip() if item_col is not None and item_col < C else ""
            if item and item.lower() != "nan":
                last_item = item
            else:
                item = last_item

            if not item:
                continue

            after_val = ""
            for cc in [after_col, after_col + 1, after_col - 1]:
                if 0 <= cc < C:
                    v = str(arr[rr][cc]).strip()
                    if v and v.lower() != "nan":
                        vn = _norm(v)
                        if vn not in ("정정후", "정정전", "정정사항", "정정항목", "항목"):
                            after_val = v
                            break

            if after_val:
                out[_norm(item)] = after_val

    return out

def scan_label_value_preferring_correction(
    dfs: List[pd.DataFrame],
    label_candidates: List[str],
    corr_after: Optional[Dict[str, str]] = None
) -> str:
    if corr_after:
        cand_norm = [_norm(x) for x in label_candidates]

        for c in cand_norm:
            v = corr_after.get(c, "")
            if str(v).strip():
                return str(v).strip()

        for k, v in corr_after.items():
            if not str(v).strip():
                continue
            if any(c in k for c in cand_norm):
                return str(v).strip()

    return scan_label_value(dfs, label_candidates)

def parse_rights_issue_record(
    dfs: List[pd.DataFrame],
    title: str,
    acpt_no: str,
    link: str,
    corr_after: Optional[Dict[str, str]] = None
) -> dict:
    rec = {k: "" for k in RIGHTS_COLUMNS}
    rec["접수번호"] = acpt_no
    rec["링크"] = link

    # 회사명/시장
    rec["회사명"] = scan_label_value_preferring_correction(dfs, ["회 사 명", "회사명", "회사 명"], corr_after) or company_from_title(title)
    rec["상장시장"] = scan_label_value_preferring_correction(dfs, ["상장시장", "시장구분", "시장 구분"], corr_after) or market_from_title(title)

    # 결의일
    rec["이사회결의일"] = scan_label_value_preferring_correction(
        dfs,
        ["15. 이사회결의일(결정일)", "이사회결의일(결정일)", "이사회결의일", "결정일"],
        corr_after
    )
    rec["최초 이사회결의일"] = scan_label_value_preferring_correction(
        dfs, ["최초 이사회결의일", "최초이사회결의일"], corr_after
    ) or rec["이사회결의일"]

    # 증자방식
    rec["증자방식"] = scan_label_value_preferring_correction(dfs, ["5. 증자방식", "증자방식", "발행방법", "배정방식"], corr_after)

    # 주식수
    issue_txt = scan_label_value_preferring_correction(
        dfs,
        ["1. 신주의 종류와 수", "신주의 종류와 수", "신주의종류와수", "신주의 종류 및 수", "신주의종류및수"],
        corr_after
    )
    prev_txt = scan_label_value_preferring_correction(
        dfs,
        ["증자전발행주식총수", "증자전 발행주식총수", "증자전발행주식총수(보통주식)", "발행주식총수", "발행주식 총수"],
        corr_after
    )

    issue_shares = _to_int(issue_txt) or _max_int_in_text(issue_txt) or \
        find_row_best_int(dfs, ["신주의종류와수", "보통주식"]) or find_row_best_int(dfs, ["보통주식", "(주)"])
    prev_shares = _to_int(prev_txt) or _max_int_in_text(prev_txt) or \
        find_row_best_int(dfs, ["증자전발행주식총수", "보통주식"]) or find_row_best_int(dfs, ["발행주식총수", "보통주식"])

    if issue_shares:
        rec["발행상품"] = "보통주식"
        rec["신규발행주식수"] = f"{issue_shares:,}"
    if prev_shares:
        rec["증자전 주식수"] = f"{prev_shares:,}"

    # 발행가/기준주가/할인율
    price_txt = scan_label_value_preferring_correction(
        dfs,
        ["6. 신주 발행가액", "신주 발행가액", "신주발행가액", "신주 발행가액(원)", "신주발행가액(원)"],
        corr_after
    )
    price = _to_int(price_txt) or find_row_best_int(dfs, ["신주발행가액", "보통주식"]) or find_row_best_int(dfs, ["신주", "발행가액"])
    rec["확정발행가(원)"] = f"{price:,}" if price else price_txt

    base_txt = scan_label_value_preferring_correction(dfs, ["7. 기준주가", "기준주가"], corr_after)
    base_price = _to_int(base_txt) or find_row_best_int(dfs, ["기준주가", "보통주식"]) or find_row_best_int(dfs, ["기준주가"])
    rec["기준주가"] = f"{base_price:,}" if base_price else base_txt

    disc_txt = scan_label_value_preferring_correction(
        dfs,
        ["7-2. 기준주가에 대한 할인율 또는 할증율 (%)", "기준주가에 대한 할인율 또는 할증율 (%)", "할인율또는할증율", "기준주가에대한할인율또는할증율"],
        corr_after
    )
    disc = _to_float(disc_txt)
    if disc is None:
        disc = find_row_best_float(dfs, ["기준주가에대한할인율또는할증율"]) or find_row_best_float(dfs, ["할인율또는할증율"])
    rec["할인(할증률)"] = f"{disc}" if disc is not None else disc_txt

    # 일정
    rec["납입일"] = scan_label_value_preferring_correction(dfs, ["9. 납입일", "납입일"], corr_after)
    rec["신주의 배당기산일"] = scan_label_value_preferring_correction(dfs, ["10. 신주의 배당기산일", "신주의 배당기산일", "배당기산일"], corr_after)
    rec["신주의 상장 예정일"] = scan_label_value_preferring_correction(dfs, ["12. 신주의 상장 예정일", "신주의 상장 예정일", "상장예정일"], corr_after)

    # 자금용도/투자자
    rec["자금용도"] = scan_label_value_preferring_correction(dfs, ["4. 자금조달의 목적", "자금조달의 목적", "자금용도"], corr_after) or build_fund_use_text(dfs)
    rec["투자자"] = extract_investors(dfs, corr_after=corr_after)

    # 백업 계산
    sh = _to_int(rec["신규발행주식수"])
    pr = _to_int(rec["확정발행가(원)"])
    if sh and pr:
        rec["확정발행금액(억원)"] = f"{(sh * pr) / 100_000_000:,.2f}"

    pv = _to_int(rec["증자전 주식수"])
    if sh and pv and pv > 0:
        rec["증자비율"] = f"{sh / pv * 100:.2f}%"

    return rec

# ==========================================================
# DART: cache + match + same-report check + apply (DART-first only when same report)
# ==========================================================
DART_CLS_MAP = {"Y": "유가증권", "K": "코스닥", "N": "코넥스", "E": "기타"}

def _dart_get_json(url: str, params: dict) -> dict:
    r = requests.get(url, params=params, timeout=DART_TIMEOUT)
    r.raise_for_status()
    return r.json()

def dart_prefetch_yusang(api_key: str, lookback_days: int):
    """최근 N일 '유상증자결정' list + corp_code별 piicDecsn 캐시"""
    end = datetime.now()
    start = end - timedelta(days=lookback_days)
    bgn_de = start.strftime("%Y%m%d")
    end_de = end.strftime("%Y%m%d")

    list_url = "https://opendart.fss.or.kr/api/list.json"
    list_params = {
        "crtfc_key": api_key,
        "bgn_de": bgn_de,
        "end_de": end_de,
        "pblntf_ty": "B",
        "pblntf_detail_ty": "B001",
        "last_reprt_at": "Y",
        "page_no": 1,
        "page_count": 100,
    }

    try:
        data = _dart_get_json(list_url, list_params)
    except Exception as e:
        print(f"[DART] list.json 실패: {e}")
        return [], {}

    if data.get("status") != "000":
        print(f"[DART] list.json status={data.get('status')} msg={data.get('message')}")
        return [], {}

    filings = [f for f in (data.get("list", []) or []) if "유상증자결정" in (f.get("report_nm") or "")]
    corp_codes = sorted({f.get("corp_code") for f in filings if f.get("corp_code")})

    piic_map: Dict[str, dict] = {}
    for corp_code in corp_codes:
        piic_url = "https://opendart.fss.or.kr/api/piicDecsn.json"
        piic_params = {
            "crtfc_key": api_key,
            "corp_code": corp_code,
            "bgn_de": bgn_de,
            "end_de": end_de,
        }
        try:
            pdat = _dart_get_json(piic_url, piic_params)
        except Exception:
            continue

        if pdat.get("status") != "000":
            continue

        for row in (pdat.get("list", []) or []):
            rno = str(row.get("rcept_no") or "").strip()
            if rno:
                piic_map[rno] = row

        time.sleep(0.2)

    print(f"[DART] cache: filings={len(filings)} piic_rows={len(piic_map)} range={bgn_de}-{end_de}")
    return filings, piic_map

def dart_match_for_kind(rec: dict, filings: List[dict]) -> Optional[dict]:
    """회사명 + 날짜(근접)로 후보 1개 선택"""
    cname = _norm_company(rec.get("회사명", ""))
    if not cname:
        return None

    board = rec.get("이사회결의일") or rec.get("최초 이사회결의일") or ""
    bdt = _safe_dt_yyyymmdd(board)

    cands = []
    for f in filings:
        fc = _norm_company(f.get("corp_name", ""))
        if not fc:
            continue
        if fc == cname or fc in cname or cname in fc:
            cands.append(f)

    if not cands:
        return None

    if bdt:
        def score(f):
            rdt = _safe_dt_yyyymmdd(f.get("rcept_dt", ""))
            return abs((rdt - bdt).days) if rdt else 9999
        cands.sort(key=score)
        return cands[0]

    cands.sort(key=lambda x: x.get("rcept_dt", ""), reverse=True)
    return cands[0]

def is_same_report(kind_rec: dict, dart_filing: dict, max_days: int) -> bool:
    """
    ✅ "똑같은 보고서" 판정:
    1) 보고서명(유상증자결정)
    2) 회사명(정규화)
    3) 날짜 근접(KIND 이사회결의일 vs DART 접수일)
    """
    report_nm = (dart_filing.get("report_nm") or "")
    if "유상증자결정" not in report_nm:
        return False

    kc = _norm_company(kind_rec.get("회사명", ""))
    dc = _norm_company(dart_filing.get("corp_name", ""))
    if not kc or not dc:
        return False

    if not (kc == dc or kc in dc or dc in kc):
        return False

    kdt = _safe_dt_yyyymmdd(kind_rec.get("이사회결의일") or kind_rec.get("최초 이사회결의일") or "")
    ddt = _safe_dt_yyyymmdd(dart_filing.get("rcept_dt") or "")
    if kdt and ddt:
        if abs((ddt - kdt).days) > max_days:
            return False

    return True

def dart_extract_xml_details(api_key: str, rcept_no: str) -> Dict[str, str]:
    """document.xml ZIP에서 확정발행가/기준주가/할인율 추출"""
    url = "https://opendart.fss.or.kr/api/document.xml"
    params = {"crtfc_key": api_key, "rcept_no": rcept_no}

    out = {"issue_price": "", "base_price": "", "discount": ""}

    try:
        res = requests.get(url, params=params, stream=True, timeout=DART_TIMEOUT)
        if res.status_code != 200:
            return out

        with zipfile.ZipFile(io.BytesIO(res.content)) as z:
            xmls = [n for n in z.namelist() if n.endswith(".xml")]
            if not xmls:
                return out
            with z.open(xmls[0]) as f:
                xml_content = f.read().decode("utf-8", errors="ignore")

        soup = BeautifulSoup(xml_content, "html.parser")
        raw_text = soup.get_text(separator=" ", strip=True)

        # 발행가액
        for pat in [
            r"(?:신주\s*)?발행가액[^\d]*([0-9]{1,3}(?:,[0-9]{3})*)",
            r"신주\s*발행가[^\d]*([0-9]{1,3}(?:,[0-9]{3})*)",
        ]:
            m = re.search(pat, raw_text)
            if m:
                out["issue_price"] = m.group(1).strip()
                break

        # 기준주가
        m = re.search(r"기준주가[^\d]*([0-9]{1,3}(?:,[0-9]{3})*)", raw_text)
        if m:
            out["base_price"] = m.group(1).strip()

        # 할인/할증률 (부호 포함)
        for pat in [
            r"(?:할인율|할증율)[^\d\+\-]*([\-+]?\d+(?:\.\d+)?)\s*%?",
            r"기준주가[^\d]{0,20}(?:할인율|할증율)[^\d\+\-]*([\-+]?\d+(?:\.\d+)?)\s*%?",
        ]:
            m = re.search(pat, raw_text)
            if m:
                out["discount"] = m.group(1).strip() + "%"
                break

    except Exception:
        return out

    return out

def apply_dart_core_fields(rec: dict, dart_filing: dict, piic_row: Optional[dict], xml_data: Optional[dict]):
    """
    ✅ 같은 보고서로 판정된 경우에만 호출!
    핵심 8개 컬럼 DART-first 덮어쓰기
    """
    # 상장시장(DART 우선)
    corp_cls = str(dart_filing.get("corp_cls") or "").strip()
    if corp_cls:
        rec["상장시장"] = DART_CLS_MAP.get(corp_cls, rec.get("상장시장", ""))

    def to0(x):
        try:
            s = str(x).replace(",", "").strip()
            return int(float(s)) if s else 0
        except:
            return 0

    # piicDecsn 기반: 신규발행주식수 / 증자전주식수 / 증자비율 / 자금용도 / 확발금(억원)
    if piic_row:
        new_shares = to0(piic_row.get("nstk_ostk_cnt")) + to0(piic_row.get("nstk_estk_cnt"))
        old_shares = to0(piic_row.get("bfic_tisstk_ostk")) + to0(piic_row.get("bfic_tisstk_estk"))

        if new_shares > 0:
            rec["신규발행주식수"] = _fmt_int(new_shares)
        if old_shares > 0:
            rec["증자전 주식수"] = _fmt_int(old_shares)
        if new_shares > 0 and old_shares > 0:
            rec["증자비율"] = f"{(new_shares / old_shares * 100):.2f}%"

        # 자금용도/확발금(억원): 6종 합
        purpose_fields = [
            ("fdpp_fclt", "시설자금"),
            ("fdpp_bsninh", "영업양수자금"),
            ("fdpp_op", "운영자금"),
            ("fdpp_dtrp", "채무상환자금"),
            ("fdpp_ocsa", "타법인증권취득자금"),
            ("fdpp_etc", "기타자금"),
        ]
        total = 0
        names = []
        for k, label in purpose_fields:
            v = to0(piic_row.get(k))
            if v > 0:
                names.append(label)
                total += v

        if total > 0:
            rec["자금용도"] = ", ".join(names)
            rec["확정발행금액(억원)"] = _fmt_amt_uk(total)

    # document.xml 기반: 확정발행가/기준주가/할인율
    if xml_data:
        if xml_data.get("issue_price"):
            rec["확정발행가(원)"] = xml_data["issue_price"]
        if xml_data.get("base_price"):
            rec["기준주가"] = xml_data["base_price"]
        if xml_data.get("discount"):
            rec["할인(할증률)"] = xml_data["discount"]

# ==========================================================
# Main
# ==========================================================
def run():
    _, rights_ws, seen_ws = gs_open()

    # 시트 값 로드(인덱스)
    values = load_sheet_values(rights_ws, RIGHTS_COLUMNS)
    last_row_ref = [len(values)]
    rights_index = build_acpt_index_from_values(values, RIGHTS_COLUMNS, key_field="접수번호")
    event_index = build_event_index_from_values(values, RIGHTS_COLUMNS)

    # seen map (스킵/로그용)
    seen_map = load_seen_map(seen_ws)
    seen_set = set(seen_map.keys())

    # DART 캐시(런 시작 시 1회)
    dart_filings, dart_piic_map = [], {}
    xml_cache: Dict[str, Dict[str, str]] = {}
    if DART_API_KEY:
        dart_filings, dart_piic_map = dart_prefetch_yusang(DART_API_KEY, DART_LOOKBACK_DAYS)
    else:
        print("[DART] DART_API_KEY 없음 -> DART 보정 없이 KIND만 실행")

    # 대상 선정
    if RUN_ONE_ACPTNO:
        targets = [Target(acpt_no=RUN_ONE_ACPTNO, title=f"[MANUAL]{RUN_ONE_ACPTNO}", link="")]
    else:
        targets = parse_rss_targets()
        # ✅ SKIP_SEEN=false면 여기서 필터링 안 함 → 매번 업데이트 가능
        if SKIP_SEEN:
            targets = [t for t in targets if t.acpt_no not in seen_set]
        targets = targets[:LIMIT] if LIMIT > 0 else targets

    if not targets:
        print("[INFO] 처리할 대상이 없습니다.")
        return

    with sync_playwright() as p:
        browser = p.chromium.launch(
            headless=HEADLESS,
            args=["--disable-blink-features=AutomationControlled", "--no-sandbox"],
        )
        context = browser.new_context(
            locale="ko-KR",
            user_agent="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120 Safari/537.36",
            viewport={"width": 1400, "height": 900},
        )

        ok = 0
        for t in targets:
            try:
                dfs, kind_url = scrape_one(context, t)

                if "유상증자" in (t.title or ""):
                    corr_after = None
                    if is_correction_title(t.title):
                        corr_after = extract_correction_after_map(dfs)

                    # 1) KIND 메인 레코드 생성
                    rec = parse_rights_issue_record(dfs, t.title, t.acpt_no, kind_url, corr_after=corr_after)

                    # 2) DART가 있으면 같은 보고서인지 확인 후, 같으면 DART 우선 덮기
                    if dart_filings:
                        filing = dart_match_for_kind(rec, dart_filings)
                        if filing and is_same_report(rec, filing, SAME_REPORT_MAX_DAYS):
                            rcept_no = str(filing.get("rcept_no") or "").strip()
                            piic_row = dart_piic_map.get(rcept_no)

                            xml_data = None
                            if rcept_no and DART_API_KEY:
                                if rcept_no in xml_cache:
                                    xml_data = xml_cache[rcept_no]
                                else:
                                    xml_data = dart_extract_xml_details(DART_API_KEY, rcept_no)
                                    xml_cache[rcept_no] = xml_data

                            apply_dart_core_fields(rec, filing, piic_row, xml_data)

                            # 링크: KIND + DART 함께
                            if rcept_no:
                                dart_link = f"https://dart.fss.or.kr/dsaf001/main.do?rcpNo={rcept_no}"
                                rec["링크"] = f"{kind_url} | {dart_link}"

                            print(f"[DART-APPLIED] company={rec.get('회사명')} rcept_no={rcept_no} piic={'Y' if piic_row else 'N'}")
                        else:
                            # 같은 보고서로 확정 못 하면 KIND 유지
                            if filing:
                                print(f"[DART-SKIP] not-same-report company={rec.get('회사명')} rcept_dt={filing.get('rcept_dt')} board={rec.get('이사회결의일')}")
                            else:
                                print(f"[DART-SKIP] no-match company={rec.get('회사명')} board={rec.get('이사회결의일')}")

                    # 3) 시트 업데이트(정정이면 event_key로 기존행 찾아 덮어쓰기)
                    if is_correction_title(t.title):
                        evk = make_event_key(
                            rec.get("회사명", ""),
                            rec.get("최초 이사회결의일", "") or rec.get("이사회결의일", ""),
                            rec.get("증자방식", "")
                        )

                        target_row = None
                        old_acpt = ""

                        if evk in event_index:
                            target_row, old_acpt = event_index[evk]
                        elif rec["접수번호"] in rights_index:
                            target_row = rights_index[rec["접수번호"]]

                        if target_row:
                            update_row(rights_ws, RIGHTS_COLUMNS, target_row, rec)

                            if old_acpt and old_acpt in rights_index and old_acpt != rec["접수번호"]:
                                del rights_index[old_acpt]
                            rights_index[rec["접수번호"]] = target_row
                            event_index[evk] = (target_row, rec["접수번호"])

                            print(f"[OK] {t.acpt_no} correction=Y mode=UPDATE row={target_row}")
                        else:
                            mode, row = upsert(rights_ws, RIGHTS_COLUMNS, rights_index, rec, key_field="접수번호", last_row_ref=last_row_ref)
                            event_index[evk] = (row, rec["접수번호"])
                            print(f"[OK] {t.acpt_no} correction=Y mode={mode.upper()} row={row}")
                    else:
                        mode, row = upsert(rights_ws, RIGHTS_COLUMNS, rights_index, rec, key_field="접수번호", last_row_ref=last_row_ref)

                        evk = make_event_key(
                            rec.get("회사명", ""),
                            rec.get("최초 이사회결의일", "") or rec.get("이사회결의일", ""),
                            rec.get("증자방식", "")
                        )
                        event_index[evk] = (row, rec["접수번호"])

                        print(f"[OK] {t.acpt_no} correction=N mode={mode.upper()} row={row}")

                # 4) seen은 스킵용이 아니라 “처리 로그(ts 갱신)” 용
                upsert_seen(seen_ws, seen_map, t.acpt_no)
                ok += 1

            except Exception as e:
                print(f"[FAIL] {t.acpt_no} {t.title} :: {e}")

            time.sleep(0.4)

        context.close()
        browser.close()

    print(f"[DONE] ok={ok}")
