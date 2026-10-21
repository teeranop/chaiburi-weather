#!/usr/bin/env python3
"""
fetch_data.py — รวบรวมข้อมูลน้ำท่วม/ฝน/เตือนภัย อ.ชัยบุรี จ.สุราษฎร์ธานี

แหล่งข้อมูล
  - GISTDA Disaster API   : พื้นที่น้ำท่วมจากดาวเทียม 1/3/7/30 วัน + น้ำท่วมซ้ำซาก (ต้องมี API key)
  - กรมอุตุนิยมวิทยา (TMD) : ผลตรวจราย 3 ชม., ฝน 24 ชม. (07:00), ข่าวเตือนภัย,
                             พยากรณ์ NWP รายชั่วโมง 24 ชม. + รายวัน 7 วัน, สภาพอากาศปัจจุบัน (current)
  - ThaiWater (สสน.)       : ฝน 24 ชม. จากสถานีโทรมาตร (ใช้คำนวณระดับสถานการณ์)

ผลลัพธ์ (โฟลเดอร์ --out, ค่าเริ่มต้น data/)
  summary.json     สรุประดับสถานการณ์ + เหตุผล
  flood.json       สถิติน้ำท่วมรายช่วงเวลา/รายตำบล (ไม่มี geometry)
  flood_map.json   GeoJSON พื้นที่น้ำท่วมสำหรับแผนที่ (ตัดทศนิยมพิกัดแล้ว)
  flood_freq.json  สรุปพื้นที่น้ำท่วมซ้ำซากตามจำนวนครั้ง (ดึงใหม่ทุก 7 วัน)
  tmd.json         ข้อมูลกรมอุตุฯ

ตัวแปรสภาพแวดล้อม (ไม่บังคับทุกตัว — ตัวไหนไม่มี ระบบจะข้ามแหล่งนั้น)
  GISTDA_API_KEY        API key จาก api-gateway.gistda.or.th
  TMD_UID, TMD_UKEY     uid/ukey ที่ลงทะเบียนกับ data.tmd.go.th (ไม่ตั้ง = ใช้ demo/demokey)
  TMD_NWP_TOKEN         Bearer token ของ TMD NWP API (พยากรณ์ 7 วันรายพิกัด)
  TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID   ส่งแจ้งเตือนเมื่อระดับเปลี่ยน/มีข่าวเตือนใหม่
  MOPH_CLIENT_ID, MOPH_SECRET           Client_ID / Secret จาก CMS MOPH Notify — ส่งแจ้งเตือนเดียวกันเข้า LINE (LINE OA หมอพร้อม)
  MOPH_NOTIFY_URL       เปลี่ยน endpoint ของ MOPH Notify (ค่าเริ่มต้น morpromt2f.moph.go.th/api/notify/send)
  DAILY_REPORT=true     บังคับส่งรายงานสรุปประจำวันทาง Telegram
  PAGE_URL              ลิงก์หน้าเว็บที่แนบในข้อความ Telegram

ใช้เฉพาะไลบรารีมาตรฐานของ Python 3.9+ ไม่ต้องติดตั้งแพ็กเกจเพิ่ม
สคริปต์ไม่ทำให้ build ล้มเมื่อแหล่งใดแหล่งหนึ่งล่ม: จะใช้ข้อมูลรอบก่อน (ถ้ามี) และทำเครื่องหมาย stale
"""
from __future__ import annotations

import argparse
import html
import json
import math
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timedelta, timezone

# ---------------------------------------------------------------- พื้นที่เป้าหมาย
LAT, LON = 8.46278, 99.07667                      # ที่ว่าการอ.ชัยบุรี
AMPHOE_CODE = "8418"                               # รหัสอำเภอชัยบุรี (กรมการปกครอง)
PROVINCE_CODE = "84"                               # สุราษฎร์ธานี
AMPHOE_TH = "ชัยบุรี"
PROVINCE_TH = "สุราษฎร์ธานี"
# กรอบแผนที่ (west, south, east, north) ครอบอำเภอ + พื้นที่ข้างเคียงเล็กน้อย
BBOX = (98.85, 8.25, 99.30, 8.70)
THAIWATER_RADIUS_KM = 40
TMD_RADIUS_KM = 150
TMD_STATION_LIMIT = 6

GISTDA_BASE = "https://api-gateway.gistda.or.th/api/2.0/resources"
GISTDA_PERIODS = ["1day", "3days", "7days", "30days"]
GISTDA_PAGE = 1000
GISTDA_MAX_PAGES = 20
FREQ_MAX_PAGES = 15
FREQ_REFRESH_DAYS = 7
MAP_MAX_FEATURES = 4000
COORD_DP = 5

TMD_BASE = "https://data.tmd.go.th/api"
TMD_NWP_DAILY = "https://data.tmd.go.th/nwpapi/v1/forecast/location/daily/at"
TMD_NWP_HOURLY = "https://data.tmd.go.th/nwpapi/v1/forecast/location/hourly/at"
NWP_HOURS = 24
THAIWATER_PUBLIC = "https://api-v3.thaiwater.net/api/v1/thaiwater30/public"
THAIWATER_RAIN = f"{THAIWATER_PUBLIC}/rain_24h"
THAIWATER_WL = f"{THAIWATER_PUBLIC}/waterlevel_load"
RAIN_STN_ID, RAIN_STN_NAME = 827, "อบต.ชัยบุรี"         # สถานีฝนสะสมย้อนหลัง (ตรงกับกราฟในหน้าเว็บ)
MOPH_NOTIFY_URL = "https://morpromt2f.moph.go.th/api/notify/send"   # MOPH Notify (LINE OA หมอพร้อม)
THAIWATER_DAM ="https://api-v3.thaiwater.net/api/v1/thaiwater30/analyst/dam"
WL_AMPHOE = ("ชัยบุรี", "พระแสง", "เขาพนม")            # อำเภอที่รายงานสถานีระดับน้ำ
WL_MAX_AGE_H = 24                                    # ไม่ใช้ค่าระดับน้ำที่เก่ากว่านี้
# อ.เขาพนม จ.กระบี่ ติดต่อกับชัยบุรี น้ำจากเขาพนมมีผลกับปริมาณน้ำของชัยบุรี
KP_AMPHOE, KP_PROVINCE = "เขาพนม", "กระบี่"

TZ_TH = timezone(timedelta(hours=7))
UA = "chaiburi-weather/1.0 (+https://github.com/teeranop/chaiburi-weather)"

# เกณฑ์ฝนของกรมอุตุนิยมวิทยา (มม./24 ชม.)
RAIN_HEAVY = 35.1
RAIN_VERY_HEAVY = 90.1
RAIN7_SATURATED = 200          # ฝนสะสม 7 วัน (มม.) ที่ถือว่าดินอิ่มน้ำ
RAIN_1H_INTENSE = 30           # ฝนรายชั่วโมง (มม.) ที่เสี่ยงน้ำท่วมฉับพลัน
WL_WATCH, WL_WARN = 80, 100    # ระดับน้ำ % ของตลิ่ง: เฝ้าระวัง / เตือนภัย (ล้นตลิ่ง)

# รหัสสภาพอากาศ (cond) ของ TMD NWP
TMD_COND = {
    1: "ท้องฟ้าแจ่มใส", 2: "มีเมฆบางส่วน", 3: "เมฆเป็นส่วนมาก", 4: "มีเมฆมาก",
    5: "ฝนตกเล็กน้อย", 6: "ฝนปานกลาง", 7: "ฝนตกหนัก", 8: "ฝนฟ้าคะนอง",
    9: "อากาศหนาวจัด", 10: "อากาศหนาว", 11: "อากาศเย็น", 12: "อากาศร้อนจัด",
}

LEVELS = [
    {"level": 0, "key": "normal", "label": "ปกติ", "color": "#15803d"},
    {"level": 1, "key": "watch", "label": "เฝ้าระวัง", "color": "#ca8a04"},
    {"level": 2, "key": "warning", "label": "เตือนภัย", "color": "#ea580c"},
    {"level": 3, "key": "critical", "label": "วิกฤต", "color": "#dc2626"},
]


# ================================================================ utilities
def log(*a):
    print("[fetch]", *a, file=sys.stderr, flush=True)


def now_th() -> datetime:
    return datetime.now(TZ_TH)


def iso(dt: datetime) -> str:
    return dt.isoformat(timespec="seconds")


def mask(url: str) -> str:
    """ซ่อนค่า key/token ใน URL ก่อนพิมพ์ log"""
    return re.sub(r"(api_key|ukey|uid|token)=[^&]+", r"\1=***", url, flags=re.I)


def http_json(url: str, params: dict | None = None, headers: dict | None = None,
              timeout: int = 60, retries: int = 2):
    if params:
        url = url + ("&" if "?" in url else "?") + urllib.parse.urlencode(params)
    h = {"User-Agent": UA, "Accept": "application/json"}
    if headers:
        h.update(headers)
    last = None
    for attempt in range(retries + 1):
        try:
            req = urllib.request.Request(url, headers=h)
            with urllib.request.urlopen(req, timeout=timeout) as r:
                raw = r.read()
            return json.loads(raw.decode("utf-8-sig"))
        except urllib.error.HTTPError as e:
            last = f"HTTP {e.code}"
            if e.code in (400, 401, 403, 404):
                break                                   # ไม่ต้องลองซ้ำ
        except Exception as e:                          # noqa: BLE001
            last = f"{type(e).__name__}: {e}"
        if attempt < retries:
            time.sleep(3 * (attempt + 1))
    raise RuntimeError(f"{last} ({mask(url)})")


def num(v):
    """แปลงค่าตัวเลขที่อาจมาเป็น dict ({'Value':..,'Unit':..}) หรือสตริง"""
    if isinstance(v, dict):
        for k in ("Value", "value", "#text", "$"):
            if k in v:
                return num(v[k])
        return None
    if v is None or v == "":
        return None
    try:
        f = float(str(v).replace(",", "").strip())
    except ValueError:
        return None
    return None if math.isnan(f) else f


def text(v):
    if isinstance(v, dict):
        for k in ("Value", "value", "#text", "$"):
            if k in v:
                return text(v[k])
        return ""
    return "" if v is None else str(v).strip()


def haversine(lat1, lon1, lat2, lon2):
    r = math.radians
    dlat, dlon = r(lat2 - lat1), r(lon2 - lon1)
    a = math.sin(dlat / 2) ** 2 + math.cos(r(lat1)) * math.cos(r(lat2)) * math.sin(dlon / 2) ** 2
    return 2 * 6371 * math.asin(math.sqrt(a))


def write_json(path: str, obj):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, separators=(",", ":"))
    os.replace(tmp, path)


def load_prev(name: str, out_dir: str, prev_url: str | None):
    """อ่านผลรอบก่อน: จากไฟล์ในเครื่องก่อน ไม่มีค่อยดึงจากหน้าเว็บที่เผยแพร่อยู่"""
    p = os.path.join(out_dir, name)
    if os.path.exists(p):
        try:
            with open(p, encoding="utf-8") as f:
                return json.load(f)
        except Exception:                               # noqa: BLE001
            pass
    if prev_url:
        try:
            return http_json(prev_url.rstrip("/") + "/" + name, timeout=30, retries=0)
        except Exception as e:                          # noqa: BLE001
            log(f"ไม่มีข้อมูลรอบก่อนของ {name}: {e}")
    return None


def mark_stale(prev: dict | None, err: str):
    if not prev:
        return None
    prev = dict(prev)
    prev["stale"] = True
    prev["error"] = err
    return prev


# ================================================================ GISTDA
def gistda_get_all(path: str, key: str, params: dict, max_pages: int, timeout: int = 90):
    feats, offset, matched = [], 0, None
    for _ in range(max_pages):
        q = dict(params, limit=GISTDA_PAGE, offset=offset)
        data = http_json(f"{GISTDA_BASE}{path}", q, {"API-Key": key}, timeout=timeout)
        page = data.get("features") or []
        matched = data.get("numberMatched", matched)
        feats.extend(page)
        if len(page) < GISTDA_PAGE:
            break
        offset += GISTDA_PAGE
    return feats, matched


def in_district(p: dict) -> bool:
    ap = str(p.get("ap_idn") or "").strip()
    if ap == AMPHOE_CODE:
        return True
    return (str(p.get("ap_tn") or "").strip() == AMPHOE_TH
            and str(p.get("pv_tn") or "").strip() == PROVINCE_TH)


def sat_date(file_name: str):
    m = re.search(r"(20\d{2})(\d{2})(\d{2})", file_name or "")
    return f"{m.group(1)}-{m.group(2)}-{m.group(3)}" if m else None


def round_coords(c):
    if isinstance(c, (int, float)):
        return round(c, COORD_DP)
    return [round_coords(x) for x in c]


def summarize_flood(feats: list) -> dict:
    """สรุปสถิติ: พื้นที่ (ไร่) รวม + ประชากร/อาคาร/รพ./รร. นับครั้งเดียวต่อ H3 cell"""
    def block(fs):
        area_m2 = sum(num(f.get("properties", {}).get("f_area")) or 0 for f in fs)
        cells = {}
        for f in fs:
            p = f.get("properties", {})
            key = p.get("h3_address") or p.get("_id") or id(f)
            c = cells.setdefault(key, {"population": 0, "building": 0, "hospital": 0, "school": 0})
            for k in c:
                c[k] = max(c[k], num(p.get(k)) or 0)
        tot = {k: sum(c[k] for c in cells.values()) for k in ("population", "building", "hospital", "school")}
        return {
            "features": len(fs),
            "area_rai": round(area_m2 / 1600, 1),
            "population": round(tot["population"]),
            "building": round(tot["building"]),
            "hospital": round(tot["hospital"]),
            "school": round(tot["school"]),
        }

    district = [f for f in feats if in_district(f.get("properties", {}))]

    by_tb = {}
    for f in district:
        p = f.get("properties", {})
        tb = str(p.get("tb_tn") or "-").strip()
        t = by_tb.setdefault(tb, {"tambon": tb, "tb_idn": str(p.get("tb_idn") or ""), "_f": []})
        t["_f"].append(f)
    tambons = []
    for t in by_tb.values():
        s = block(t.pop("_f"))
        tambons.append({**t, **s})
    tambons.sort(key=lambda x: -x["area_rai"])

    dates = sorted({d for d in (sat_date(f.get("properties", {}).get("file_name")) for f in feats) if d})
    return {
        "district": block(district),
        "bbox": block(feats),
        "tambons": tambons,
        "satellite_dates": dates[-5:],
        "latest_satellite_date": dates[-1] if dates else None,
    }


def to_map_features(feats: list, period: str) -> list:
    out = []
    for f in feats[:MAP_MAX_FEATURES]:
        g = f.get("geometry")
        if not g or "coordinates" not in g:
            continue
        p = f.get("properties", {})
        out.append({
            "type": "Feature",
            "geometry": {"type": g.get("type"), "coordinates": round_coords(g["coordinates"])},
            "properties": {
                "p": period,
                "tb": p.get("tb_tn"),
                "ap": p.get("ap_tn"),
                "rai": round((num(p.get("f_area")) or 0) / 1600, 1),
                "pop": round(num(p.get("population")) or 0),
                "in": in_district(p),
                "d": sat_date(p.get("file_name")),
            },
        })
    return out


def fetch_gistda(key: str, out_dir: str, prev_url: str | None) -> tuple[dict, dict]:
    stats = {"source": "GISTDA Disaster API", "generated_at": iso(now_th()),
             "bbox": list(BBOX), "periods": {}}
    fmap = {"type": "FeatureCollection", "features": [], "generated_at": stats["generated_at"]}
    if not key:
        stats["error"] = "ยังไม่ได้ตั้งค่า GISTDA_API_KEY"
        return stats, fmap

    bbox = ",".join(str(x) for x in BBOX)
    errors = []
    for period in GISTDA_PERIODS:
        try:
            feats, matched = gistda_get_all(f"/features/flood/{period}", key, {"bbox": bbox}, GISTDA_MAX_PAGES)
            s = summarize_flood(feats)
            s["number_matched"] = matched
            s["truncated"] = bool(matched and matched > len(feats))
            stats["periods"][period] = s
            fmap["features"].extend(to_map_features(feats, period))
            log(f"GISTDA flood/{period}: {len(feats)} features, ในอำเภอ {s['district']['area_rai']} ไร่")
        except Exception as e:                          # noqa: BLE001
            errors.append(f"flood/{period}: {e}")
            log(f"GISTDA flood/{period} ล้มเหลว: {e}")

    if errors and not stats["periods"]:
        prev = load_prev("flood.json", out_dir, prev_url)
        prev_map = load_prev("flood_map.json", out_dir, prev_url)
        if prev:
            return mark_stale(prev, "; ".join(errors)), prev_map or fmap
    if errors:
        stats["error"] = "; ".join(errors)
    return stats, fmap


def fetch_flood_freq(key: str, out_dir: str, prev_url: str | None) -> dict | None:
    prev = load_prev("flood_freq.json", out_dir, prev_url)
    if prev and prev.get("generated_at"):
        try:
            age = now_th() - datetime.fromisoformat(prev["generated_at"])
            if age < timedelta(days=FREQ_REFRESH_DAYS) and not prev.get("error"):
                log(f"flood-freq: ใช้ข้อมูลเดิม (อายุ {age.days} วัน)")
                return prev
        except ValueError:
            pass
    if not key:
        return prev
    try:
        bbox = ",".join(str(x) for x in BBOX)
        feats, matched = gistda_get_all("/features/flood-freq", key, {"bbox": bbox}, FREQ_MAX_PAGES, timeout=120)
    except Exception as e:                              # noqa: BLE001
        log(f"flood-freq ล้มเหลว: {e}")
        return mark_stale(prev, str(e)) if prev else {"error": str(e), "generated_at": iso(now_th())}

    def is_chai(p):
        pv, ap = str(p.get("pv_code") or "").strip(), str(p.get("ap_code") or "").strip()
        return ap == AMPHOE_CODE or (pv == PROVINCE_CODE and ap in ("18", AMPHOE_CODE))

    def agg(fs):
        by = {}
        for f in fs:
            p = f.get("properties", {})
            fr = int(num(p.get("freq")) or 0)
            by[fr] = by.get(fr, 0) + (num(p.get("area_rai")) or 0)
        return [{"freq": k, "area_rai": round(v, 1)} for k, v in sorted(by.items())]

    chai = [f for f in feats if is_chai(f.get("properties", {}))]
    log(f"flood-freq: {len(feats)} features ในกรอบ, ในอำเภอ {len(chai)}")
    return {
        "source": "GISTDA flood-freq",
        "generated_at": iso(now_th()),
        "number_matched": matched,
        "truncated": bool(matched and matched > len(feats)),
        "district": agg(chai),
        "bbox": agg(feats),
        "district_codes_matched": len(chai) > 0,
    }


# ================================================================ TMD
def tmd_stations(payload) -> list:
    st = (payload or {}).get("Stations") or {}
    st = st.get("Station") if isinstance(st, dict) else st
    if isinstance(st, dict):
        st = [st]
    return st if isinstance(st, list) else []


def parse_tmd_dt(s: str):
    s = text(s)
    for fmt in ("%m/%d/%Y %H:%M:%S", "%Y-%m-%d %H:%M:%S", "%Y-%m-%dT%H:%M:%S", "%d/%m/%Y %H:%M:%S"):
        try:
            return datetime.strptime(s, fmt).replace(tzinfo=TZ_TH).isoformat(timespec="minutes")
        except ValueError:
            continue
    return s or None


def find_rain(obs: dict):
    """หาค่าฝนจาก Observation แบบยืดหยุ่น (ชื่อคีย์ต่างกันในแต่ละ API/เวอร์ชัน)"""
    if not isinstance(obs, dict):
        return None, None
    for k in ("Rainfall", "Rainfall24Hr", "RainfallLast24Hr", "Rain24Hr", "Rainfall24Hours"):
        if k in obs:
            return k, num(obs[k])
    for k, v in obs.items():
        if "rain" in k.lower():
            return k, num(v)
    return None, None


def parse_tmd_obs(payload) -> list:
    rows = []
    for s in tmd_stations(payload):
        lat, lon = num(s.get("Latitude")), num(s.get("Longitude"))
        if lat is None or lon is None:
            continue
        obs = s.get("Observation") or s.get("Observe") or {}
        rk, rain = find_rain(obs)
        rows.append({
            "wmo": text(s.get("WmoStationNumber")),
            "name": text(s.get("StationNameThai")) or text(s.get("StationNameEnglish")),
            "province": text(s.get("Province")),
            "lat": lat, "lon": lon,
            "dist_km": round(haversine(LAT, LON, lat, lon), 1),
            "time": parse_tmd_dt(obs.get("DateTime") or obs.get("DateTimeObserved") or ""),
            "rain": rain, "rain_key": rk,
            "rain_24h": num(obs.get("Rainfall24Hr")),
            "temp": num(obs.get("AirTemperature") or obs.get("MaxTemperature")),
            "dewpoint": num(obs.get("DewPoint")),
            "rh": num(obs.get("RelativeHumidity")),
            "wind_kmh": num(obs.get("WindSpeed")),
            "wind_dir": num(obs.get("WindDirection")),
            "pressure": num(obs.get("MeanSeaLevelPressure")),
            "visibility_km": num(obs.get("LandVisibility")),
        })
    rows = [r for r in rows if r["dist_km"] <= TMD_RADIUS_KM]
    rows.sort(key=lambda r: r["dist_km"])
    return rows[:TMD_STATION_LIMIT]


def walk_dicts(o):
    if isinstance(o, dict):
        yield o
        for v in o.values():
            yield from walk_dicts(v)
    elif isinstance(o, list):
        for v in o:
            yield from walk_dicts(v)


def pick(d: dict, *needles, prefer_thai=True):
    keys = list(d.keys())
    for n in needles:
        cand = [k for k in keys if n.lower() in k.lower()]
        if prefer_thai:
            cand.sort(key=lambda k: (0 if "thai" in k.lower() else 1, len(k)))
        for k in cand:
            t = text(d[k])
            if t:
                return t
    return ""


def parse_tmd_warnings(payload) -> list:
    out, seen = [], set()
    for d in walk_dicts(payload):
        if not any("title" in k.lower() for k in d):
            continue
        title = pick(d, "Title")
        if not title or title in seen:
            continue
        seen.add(title)
        desc = pick(d, "Description", "Detail", "Content")
        ann = pick(d, "Announce", "DateTime", "Date", prefer_thai=False)
        url = pick(d, "Document", "Url", "Link", prefer_thai=False)
        blob = f"{title} {desc}"
        out.append({
            "title": title,
            "description": re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", desc)).strip()[:1200],
            "announced": parse_tmd_dt(ann) or ann,
            "url": url if url.startswith("http") else "",
            "relevant": any(w in blob for w in (PROVINCE_TH, "ภาคใต้", AMPHOE_TH)),
        })
    out.sort(key=lambda w: w.get("announced") or "", reverse=True)
    return out[:10]


def nwp_forecasts(payload) -> list:
    """รายการ forecasts ของพิกัดแรก (daily ใช้ weather_forecast.locations, hourly ใช้ WeatherForcasts)"""
    locs = None
    if isinstance(payload, dict):
        locs = payload.get("WeatherForcasts") or payload.get("WeatherForecasts")
        if locs is None and isinstance(payload.get("weather_forecast"), dict):
            locs = payload["weather_forecast"].get("locations")
    if not locs:
        return []
    return locs[0].get("forecasts") or []


def parse_nwp_hourly(payload) -> list:
    hours = []
    for fc in nwp_forecasts(payload):
        d = fc.get("data") or {}
        cond = int(num(d.get("cond")) or 0)
        ws = num(d.get("ws10m"))
        hours.append({
            "time": str(fc.get("time", "")),
            "tc": num(d.get("tc")), "rh": num(d.get("rh")),
            "rain": num(d.get("rain")), "slp": num(d.get("slp")),
            "wind_kmh": round(ws * 3.6, 1) if ws is not None else None,   # m/s -> กม./ชม.
            "wind_dir": num(d.get("wd10m")),
            "cond": cond, "cond_th": TMD_COND.get(cond, ""),
        })
    return hours


def heat_index(t, rh):
    """อุณหภูมิที่รู้สึก (Heat Index ของ NOAA) — ใช้เมื่อร้อนกว่า 27°C เท่านั้น"""
    if t is None or rh is None:
        return None
    if t < 27:
        return t
    f = t * 9 / 5 + 32
    hi = (-42.379 + 2.04901523 * f + 10.14333127 * rh - 0.22475541 * f * rh
          - 6.83783e-3 * f * f - 5.481717e-2 * rh * rh + 1.22874e-3 * f * f * rh
          + 8.5282e-4 * f * rh * rh - 1.99e-6 * f * f * rh * rh)
    return round((hi - 32) * 5 / 9, 1)


def build_current(obs3h: list, hourly: list) -> dict | None:
    """สภาพอากาศปัจจุบัน: ค่าวัดจริงจากสถานีกรมอุตุฯ ที่ใกล้ที่สุด + สภาพท้องฟ้าจาก NWP รายชั่วโมงชั่วโมงนี้"""
    st = next((r for r in obs3h or [] if r.get("temp") is not None), None)
    nwp = hourly[0] if hourly else None
    if not st and not nwp:
        return None
    cur = {"station": st, "nwp": nwp}
    if st:
        cur["feels_like"] = heat_index(st["temp"], st.get("rh"))
    return cur


def parse_nwp_daily(payload) -> list:
    days = []
    for fc in nwp_forecasts(payload):
        d = fc.get("data") or {}
        cond = int(num(d.get("cond")) or 0)
        days.append({
            "date": str(fc.get("time", ""))[:10],
            "tmax": num(d.get("tc_max")), "tmin": num(d.get("tc_min")),
            "rain": num(d.get("rain")), "rh": num(d.get("rh")),
            "wind": num(d.get("ws10m")),
            "cond": cond, "cond_th": TMD_COND.get(cond, ""),
        })
    return days


def fetch_tmd(out_dir: str, prev_url: str | None) -> dict:
    uid = os.environ.get("TMD_UID") or "demo"
    ukey = os.environ.get("TMD_UKEY") or "demokey"
    token = os.environ.get("TMD_NWP_TOKEN", "")
    base = {"uid": uid, "ukey": ukey, "format": "json"}
    res = {"source": "กรมอุตุนิยมวิทยา (data.tmd.go.th)", "generated_at": iso(now_th()),
           "demo_key": uid == "demo", "errors": {}}
    prev = load_prev("tmd.json", out_dir, prev_url) or {}

    def attempt(name, fn):
        try:
            res[name] = fn()
        except Exception as e:                          # noqa: BLE001
            res["errors"][name] = str(e)
            log(f"TMD {name} ล้มเหลว: {e}")
            if prev.get(name):
                res[name] = prev[name]
                res.setdefault("stale", []).append(name)

    attempt("obs3h", lambda: parse_tmd_obs(http_json(f"{TMD_BASE}/Weather3Hours/V2/", base)))
    attempt("today", lambda: parse_tmd_obs(http_json(f"{TMD_BASE}/WeatherToday/V2/", base)))
    attempt("warnings", lambda: parse_tmd_warnings(http_json(f"{TMD_BASE}/WeatherWarningNews/v1/", base)))
    if token:
        attempt("forecast", lambda: parse_nwp_daily(http_json(
            TMD_NWP_DAILY,
            {"lat": LAT, "lon": LON, "fields": "tc_max,tc_min,rh,rain,ws10m,cond",
             "date": now_th().date().isoformat(), "duration": 7},
            {"Authorization": f"Bearer {token}"})))
        now = now_th()
        attempt("hourly", lambda: parse_nwp_hourly(http_json(
            TMD_NWP_HOURLY,
            {"lat": LAT, "lon": LON, "fields": "tc,rh,rain,slp,ws10m,wd10m,cond",
             "date": now.date().isoformat(), "hour": now.hour, "duration": NWP_HOURS},
            {"Authorization": f"Bearer {token}"})))
    else:
        res["errors"]["forecast"] = res["errors"]["hourly"] = "ยังไม่ได้ตั้งค่า TMD_NWP_TOKEN"
    res["current"] = build_current(res.get("obs3h"), res.get("hourly"))
    return res


# ================================================================ ThaiWater (สำหรับคำนวณระดับ)
def tw_place(geo: dict) -> dict:
    g = geo or {}
    return {"tambon": (g.get("tumbon_name") or {}).get("th") or "",
            "amphoe": (g.get("amphoe_name") or {}).get("th") or "",
            "province": (g.get("province_name") or {}).get("th") or ""}


def is_chaiburi(place: dict) -> bool:
    return place.get("amphoe") == AMPHOE_TH and place.get("province") == PROVINCE_TH


def is_khaophanom(place: dict) -> bool:
    return place.get("amphoe") == KP_AMPHOE and place.get("province") == KP_PROVINCE


def place_label(rec: dict) -> str:
    """ต.X (ในอำเภอ) หรือ ต.X อ.Y (นอกอำเภอ) — กันสับสนสถานีชื่อซ้ำ"""
    if not rec:
        return ""
    parts = [f"ต.{rec['tambon']}"] if rec.get("tambon") else []
    if rec.get("amphoe") and not is_chaiburi(rec):
        parts.append(f"อ.{rec['amphoe']}")
    return " ".join(parts)


def fetch_thaiwater_rain() -> dict:
    data = http_json(THAIWATER_RAIN, timeout=60)
    best_in, best_near, n_in, n_near = None, None, 0, 0
    int_in, int_near = None, None                     # ฝนรายชั่วโมงแรงสุด
    kp = {"stations": 0, "max_24h": None, "max_1h": None}   # อ.เขาพนม จ.กระบี่
    for x in data.get("data") or []:
        st = x.get("station") or {}
        lat, lon = num(st.get("tele_station_lat")), num(st.get("tele_station_long"))
        if lat is None or lon is None:
            continue
        place = tw_place(x.get("geocode"))
        inchai = is_chaiburi(place)
        dist = haversine(LAT, LON, lat, lon)
        r24, r1 = num(x.get("rain_24h")), num(x.get("rain_1h"))
        rec = {"name": (st.get("tele_station_name") or {}).get("th"), **place, "rain_24h": r24, "rain_1h": r1,
               "dist_km": round(dist, 1), "time": x.get("rainfall_datetime")}
        if inchai:
            n_in += 1
            if r24 is not None and (best_in is None or r24 > best_in["rain_24h"]):
                best_in = rec
            if r1 is not None and (int_in is None or r1 > int_in["rain_1h"]):
                int_in = rec
        if inchai or dist <= THAIWATER_RADIUS_KM:
            n_near += 1
            if r24 is not None and (best_near is None or r24 > best_near["rain_24h"]):
                best_near = rec
            if r1 is not None and (int_near is None or r1 > int_near["rain_1h"]):
                int_near = rec
        if is_khaophanom(place):
            kp["stations"] += 1
            if r24 is not None and (kp["max_24h"] is None or r24 > kp["max_24h"]["rain_24h"]):
                kp["max_24h"] = rec
            if r1 is not None and (kp["max_1h"] is None or r1 > kp["max_1h"]["rain_1h"]):
                kp["max_1h"] = rec
    return {"stations_in_district": n_in, "stations_nearby": n_near,
            "max_in_district": best_in, "max_nearby": best_near,
            "max_1h_in_district": int_in, "max_1h_nearby": int_near,
            "khaophanom": kp}


def wl_status(pct):
    if pct is None:
        return ""
    if pct >= WL_WARN:
        return "ล้นตลิ่ง"
    if pct >= WL_WATCH:
        return "น้ำมาก"
    if pct >= 30:
        return "ปกติ"
    return "น้ำน้อย"


def fetch_waterlevel() -> list:
    """ระดับน้ำ (% ของตลิ่ง) จากสถานีโทรมาตร ThaiWater ในอำเภอ WL_AMPHOE — เรียงจากสูงไปต่ำ"""
    data = http_json(THAIWATER_WL, timeout=90)
    rows = ((data.get("waterlevel_data") or {}).get("data")) or []
    cutoff = now_th() - timedelta(hours=WL_MAX_AGE_H)
    out = []
    for x in rows:
        st = x.get("station") or {}
        lat, lon = num(st.get("tele_station_lat")), num(st.get("tele_station_long"))
        pct = num(x.get("storage_percent"))
        if lat is None or lon is None or pct is None:
            continue
        place = tw_place(x.get("geocode"))
        if place["amphoe"] not in WL_AMPHOE:
            continue
        dist = haversine(LAT, LON, lat, lon)
        try:
            t = datetime.strptime(x.get("waterlevel_datetime") or "", "%Y-%m-%d %H:%M").replace(tzinfo=TZ_TH)
        except ValueError:
            continue
        if t < cutoff:
            continue
        name = re.sub(r"\s*\(.*?\)\s*$", "", (st.get("tele_station_name") or {}).get("th") or "")
        out.append({
            "name": name, **place, "river": x.get("river_name") or "",
            "dist_km": round(dist, 1), "time": iso(t),
            "pct": round(pct, 1), "status": wl_status(pct),
            "msl": num(x.get("waterlevel_msl")), "bank": num(st.get("min_bank")),
        })
    out.sort(key=lambda r: -r["pct"])
    return out


def fetch_kp_dams() -> list:
    """อ่างเก็บน้ำใน อ.เขาพนม จ.กระบี่ (เช่น อ่างฯ บางกำปรัด) — % ความจุล่าสุด"""
    d = http_json(THAIWATER_DAM, timeout=90).get("data") or {}
    out = []
    for x in (d.get("dam_daily") or []) + (d.get("dam_medium") or []):   # เขื่อนใหญ่ + อ่างฯ ขนาดกลาง
        place = tw_place(x.get("geocode"))
        pct = num(x.get("dam_storage_percent"))
        if not is_khaophanom(place) or pct is None:
            continue
        dam = x.get("dam") or {}
        out.append({"name": ((dam.get("dam_name") or {}).get("th") or "").strip(), **place,
                    "pct": round(pct, 1), "storage": num(x.get("dam_storage")),
                    "normal": num(dam.get("normal_storage")), "date": x.get("dam_date")})
    out.sort(key=lambda d: -d["pct"])
    return out


def fetch_rain_history() -> dict:
    """ฝนรายวันย้อนหลัง 30 วันของสถานี RAIN_STN (วันนี้ = รวมฝนรายชั่วโมงตั้งแต่ 00:00)"""
    now = now_th()
    today = now.date()
    prev = (today.replace(day=1) - timedelta(days=1))
    daily = {}
    for y, m in ((prev.year, prev.month), (today.year, today.month)):
        d = http_json(f"{THAIWATER_PUBLIC}/rain_monthly_graph",
                      {"station_id": RAIN_STN_ID, "year": y, "month": m}, timeout=60)
        for x in d.get("data") or []:
            daily[str(x.get("rainfall_datetime", ""))[:10]] = num(x.get("rainfall_value"))
    try:
        h = http_json(f"{THAIWATER_PUBLIC}/rain_24h_graph", {"station_id": RAIN_STN_ID}, timeout=60)
        hrs = [num(x.get("rainfall_value")) for x in h.get("data") or []
               if str(x.get("rainfall_datetime", "")).startswith(today.isoformat())]
        hrs = [v for v in hrs if v is not None]
        if hrs:
            daily[today.isoformat()] = round(sum(hrs), 1)
    except Exception as e:                              # noqa: BLE001
        log(f"ThaiWater rain_24h_graph ล้มเหลว: {e}")
    days = [{"date": (today - timedelta(days=i)).isoformat(),
             "rain": daily.get((today - timedelta(days=i)).isoformat())} for i in range(29, -1, -1)]
    total = lambda n: round(sum(d["rain"] or 0 for d in days[-n:]), 1)   # noqa: E731
    return {"station": RAIN_STN_NAME, "station_id": RAIN_STN_ID,
            "sum3": total(3), "sum7": total(7), "sum30": total(30),
            "missing7": sum(1 for d in days[-7:] if d["rain"] is None), "days": days}


def nwp_rain_window(hourly: list, hours: int = 24) -> dict | None:
    """สรุปฝนจาก NWP รายชั่วโมง: รวม, ชั่วโมงที่แรงสุด, ช่วงเวลาที่คาดว่าฝนตก (≥0.5 มม./ชม.)"""
    hs = [h for h in (hourly or [])[:hours] if h.get("rain") is not None]
    if not hs:
        return None
    wet = [h for h in hs if h["rain"] >= 0.5]
    peak = max(hs, key=lambda h: h["rain"])
    return {"total": round(sum(h["rain"] for h in hs), 1), "hours": len(hs),
            "peak": peak["rain"], "peak_time": peak["time"],
            "start": wet[0]["time"] if wet else None, "end": wet[-1]["time"] if wet else None}


# ================================================================ ระดับสถานการณ์
def wl_label(r: dict) -> str:
    """ชื่อสถานีระดับน้ำ เช่น "คลองอิปัน สถานีพระแสง ต.อิปัน อ.พระแสง\""""
    return " ".join(x for x in (r.get("river"), f"สถานี{r['name']}", place_label(r)) if x)


def assess(flood: dict, tmd: dict, tw: dict | None, wl: list | None = None,
           rh: dict | None = None, nwin: dict | None = None,
           kp_dams: list | None = None) -> tuple[int, list]:
    reasons, level = [], 0

    def bump(lv, why):
        nonlocal level
        level = max(level, lv)
        reasons.append({"level": lv, "text": why})

    # --- ฝน (ใช้ค่าสูงสุดในอำเภอ ถ้าไม่มีใช้รอบรัศมี)
    rain24, rain_src = None, ""
    if tw:
        b = tw.get("max_in_district") or tw.get("max_nearby")
        if b and b.get("rain_24h") is not None:
            rain24, rain_src = b["rain_24h"], f"{b['name']} {place_label(b)} (ThaiWater)"
    for r in (tmd.get("today") or [])[:2]:
        if r.get("rain") is not None and r["dist_km"] <= 60 and (rain24 is None or r["rain"] > rain24):
            rain24, rain_src = r["rain"], f"{r['name']} (กรมอุตุฯ)"
    if rain24 is not None:
        if rain24 >= 150:
            bump(3, f"ฝน 24 ชม. {rain24:.1f} มม. ที่ {rain_src} — หนักมากเกิน 150 มม.")
        elif rain24 >= RAIN_VERY_HEAVY:
            bump(2, f"ฝน 24 ชม. {rain24:.1f} มม. ที่ {rain_src} — ฝนหนักมาก")
        elif rain24 >= RAIN_HEAVY:
            bump(1, f"ฝน 24 ชม. {rain24:.1f} มม. ที่ {rain_src} — ฝนหนัก")

    # --- ฝนตกแรงรายชั่วโมง (เสี่ยงน้ำท่วมฉับพลัน)
    if tw:
        i = tw.get("max_1h_in_district") or tw.get("max_1h_nearby")
        if i and (i.get("rain_1h") or 0) >= RAIN_1H_INTENSE:
            bump(1, f"ฝนตกแรง {i['rain_1h']:.1f} มม./ชม. ที่ {i['name']} {place_label(i)} — เสี่ยงน้ำท่วมฉับพลัน")

    # --- ฝนสะสม 7 วัน (ดินอิ่มน้ำ ฝนไม่มากก็ท่วมได้)
    sum7 = (rh or {}).get("sum7")
    saturated = sum7 is not None and sum7 >= RAIN7_SATURATED
    if saturated:
        if rain24 is not None and rain24 >= RAIN_HEAVY:
            bump(2, f"ฝนหนักซ้ำขณะดินอิ่มน้ำ — ฝนสะสม 7 วัน {sum7:,.0f} มม. ({rh['station']})")
        else:
            bump(1, f"ฝนสะสม 7 วัน {sum7:,.0f} มม. ที่ {rh['station']} — ดินอิ่มน้ำ")

    # --- ระดับน้ำในคลอง/แม่น้ำ (สถานีที่สูงที่สุดรอบอำเภอ)
    if wl:
        top = wl[0]
        if top["pct"] >= WL_WARN:
            bump(2, f"ระดับน้ำ{wl_label(top)} {top['pct']:.0f}% ของตลิ่ง — ล้นตลิ่ง")
        elif top["pct"] >= WL_WATCH:
            bump(1, f"ระดับน้ำ{wl_label(top)} {top['pct']:.0f}% ของตลิ่ง — น้ำมาก")

    # --- อ.เขาพนม จ.กระบี่ (พื้นที่ติดต่อ น้ำไหลมาชัยบุรี)
    kp = (tw or {}).get("khaophanom") or {}
    k = kp.get("max_24h")
    if k and (k.get("rain_24h") or 0) >= RAIN_VERY_HEAVY:
        bump(1, f"ฝนหนักมากที่ อ.เขาพนม {k['rain_24h']:.0f} มม. ({k['name']} ต.{k['tambon']}) — น้ำอาจไหลมาชัยบุรี")
    for d in kp_dams or []:
        if d["pct"] >= 100:
            bump(1, f"{d['name']} อ.เขาพนม {d['pct']:.0f}% ของความจุ — อาจมีการระบายน้ำ")

    # --- พยากรณ์ฝน 24 ชม. ข้างหน้า (NWP กรมอุตุฯ)
    if nwin:
        if nwin["total"] >= RAIN_VERY_HEAVY:
            bump(1, f"กรมอุตุฯ คาดฝน 24 ชม. ข้างหน้า {nwin['total']:.0f} มม. — ฝนหนักมาก")
        elif nwin["total"] >= RAIN_HEAVY and saturated:
            bump(1, f"กรมอุตุฯ คาดฝน 24 ชม. ข้างหน้า {nwin['total']:.0f} มม. ขณะดินอิ่มน้ำ")

    # --- ข่าวเตือนภัยกรมอุตุฯ ที่เกี่ยวข้อง ภายใน 48 ชม.
    cutoff = now_th() - timedelta(hours=48)
    for w in tmd.get("warnings") or []:
        if not w.get("relevant"):
            continue
        try:
            t = datetime.fromisoformat(w["announced"])
            recent = t >= cutoff
        except (TypeError, ValueError):
            recent = False
        if recent:
            bump(1, f"กรมอุตุฯ ประกาศ: {w['title']}")
            break

    # --- น้ำท่วมจากดาวเทียม (ในอำเภอ)
    per = (flood or {}).get("periods") or {}
    a = {p: ((per.get(p) or {}).get("district") or {}).get("area_rai", 0) or 0 for p in GISTDA_PERIODS}
    recent_flood = max(a["1day"], a["3days"])
    if recent_flood >= 1000:
        bump(3, f"ดาวเทียมพบน้ำท่วมในอำเภอ {recent_flood:,.0f} ไร่ (1–3 วันล่าสุด)")
    elif recent_flood > 0 and rain24 is not None and rain24 >= RAIN_HEAVY:
        bump(3, f"ดาวเทียมพบน้ำท่วมในอำเภอ {recent_flood:,.0f} ไร่ และยังมีฝนหนัก")
    elif recent_flood > 0:
        bump(2, f"ดาวเทียมพบน้ำท่วมในอำเภอ {recent_flood:,.0f} ไร่ (1–3 วันล่าสุด)")
    elif a["7days"] > 0:
        bump(2, f"ดาวเทียมพบน้ำท่วมในอำเภอ {a['7days']:,.0f} ไร่ ในรอบ 7 วัน")
    elif a["30days"] > 0:
        bump(1, f"มีพื้นที่น้ำท่วมในอำเภอ {a['30days']:,.0f} ไร่ ในรอบ 30 วัน")

    reasons.sort(key=lambda r: -r["level"])
    return level, reasons


# ================================================================ Telegram
def tg_send(msg: str):
    tok, chat = os.environ.get("TELEGRAM_BOT_TOKEN"), os.environ.get("TELEGRAM_CHAT_ID")
    if not tok or not chat:
        return False
    body = urllib.parse.urlencode({"chat_id": chat, "text": msg, "parse_mode": "HTML",
                                   "disable_web_page_preview": "true"}).encode()
    try:
        req = urllib.request.Request(f"https://api.telegram.org/bot{tok}/sendMessage", data=body,
                                     headers={"User-Agent": UA})
        urllib.request.urlopen(req, timeout=30).read()
        return True
    except Exception as e:                              # noqa: BLE001
        log(f"Telegram ล้มเหลว: {type(e).__name__}")
        return False


def html_to_text(msg: str) -> str:
    """แปลงข้อความ HTML ของ Telegram เป็นข้อความธรรมดาสำหรับ LINE (LINE ไม่รองรับ HTML)"""
    msg = re.sub(r'<a href="([^"]+)">([^<]+)</a>', r"\2: \1", msg)
    return html.unescape(re.sub(r"<[^>]+>", "", msg))


def moph_post(message: dict, ck: str, sk: str) -> bool:
    url = os.environ.get("MOPH_NOTIFY_URL") or MOPH_NOTIFY_URL
    body = json.dumps({"messages": [message]}, ensure_ascii=False).encode()
    try:
        req = urllib.request.Request(url, data=body, method="POST", headers={
            "User-Agent": UA, "Content-Type": "application/json", "client-key": ck, "secret-key": sk})
        urllib.request.urlopen(req, timeout=30).read()
        return True
    except urllib.error.HTTPError as e:
        log(f"MOPH Notify ({message['type']}) ล้มเหลว: HTTP {e.code}")
    except Exception as e:                              # noqa: BLE001
        log(f"MOPH Notify ({message['type']}) ล้มเหลว: {type(e).__name__}")
    return False


def moph_send(msg: str, flex: dict | None = None):
    """ส่งเข้า LINE ผ่าน MOPH Notify (LINE OA หมอพร้อม) — ข้ามถ้าไม่ได้ตั้ง key
    ส่งเป็นการ์ด Flex ก่อน ถ้าไม่ผ่านจะส่งเป็นข้อความธรรมดาแทน"""
    # ค่า Client_ID / Secret จาก CMS MOPH Notify → ส่งเป็น header client-key / secret-key
    ck, sk = os.environ.get("MOPH_CLIENT_ID"), os.environ.get("MOPH_SECRET")
    if not ck or not sk:
        return False
    if flex and moph_post(flex, ck, sk):
        return True
    return moph_post({"type": "text", "text": html_to_text(msg)[:4900]}, ck, sk)


def notify(msg: str, flex: dict | None = None):
    """ส่งทุกช่องทางที่ตั้งค่าไว้ (Telegram = ข้อความ HTML, LINE หมอพร้อม = การ์ด Flex)"""
    sent = [name for name, ok in (("Telegram", tg_send(msg)), ("LINE หมอพร้อม", moph_send(msg, flex))) if ok]
    log("ส่งแจ้งเตือน: " + (", ".join(sent) or "ไม่มีช่องทางที่ตั้งค่าไว้"))


def esc(s) -> str:
    return str(s).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def build_message(summary: dict, flood: dict, tmd: dict, header: str) -> str:
    lv = LEVELS[summary["level"]]
    icon = ["🟢", "🟡", "🟠", "🔴"][summary["level"]]
    lines = [f"<b>{esc(header)}</b>", f"อ.{AMPHOE_TH} จ.{PROVINCE_TH}",
             f"{icon} ระดับ: <b>{lv['label']}</b>"]
    for r in summary["reasons"][:5]:
        lines.append(f"• {esc(r['text'])}")

    # ระดับน้ำ 3 สถานีที่สูงที่สุด
    wl = summary.get("waterlevel") or []
    if wl:
        lines.append("🌊 ระดับน้ำ (% ของตลิ่ง): " + " · ".join(
            f"{esc(r['name'])} {esc(place_label(r))} {r['pct']:.0f}%" for r in wl[:3]))

    # อ.เขาพนม จ.กระบี่: ฝนสูงสุด + อ่างเก็บน้ำ
    tw = summary.get("thaiwater") or {}
    kp = tw.get("khaophanom") or {}
    parts = []
    k = kp.get("max_24h")
    if k and k.get("rain_24h") is not None:
        parts.append(f"ฝน 24 ชม. สูงสุด {k['rain_24h']} มม. ({esc(k['name'])} ต.{esc(k['tambon'])})")
    parts += [f"{esc(d['name'].replace('อ่างเก็บน้ำ', 'อ่างฯ '))} {d['pct']:.0f}%" for d in summary.get("kp_dams") or []]
    if parts:
        lines.append(f"⛰️ อ.{KP_AMPHOE} จ.{KP_PROVINCE}: " + " · ".join(parts))

    # ฝน 24 ชม. / แรงสุดรายชั่วโมง / สะสม
    b = tw.get("max_in_district") or tw.get("max_nearby")
    if b:
        lines.append(f"🌧 ฝน 24 ชม. สูงสุด: {b['rain_24h']} มม. ({esc(b['name'])} {esc(place_label(b))})")
    i = tw.get("max_1h_in_district") or tw.get("max_1h_nearby")
    if i and (i.get("rain_1h") or 0) > 0:
        lines.append(f"⚡ ฝนแรงสุดชั่วโมงล่าสุด: {i['rain_1h']} มม./ชม. ({esc(i['name'])} {esc(place_label(i))})")
    rh = summary.get("rain_history") or {}
    if rh.get("sum7") is not None:
        miss = f" (ขาดข้อมูล {rh['missing7']} วัน)" if rh.get("missing7") else ""
        lines.append(f"💧 ฝนสะสม {esc(rh['station'])}: 3 วัน {rh['sum3']:,.0f} มม. · 7 วัน {rh['sum7']:,.0f} มม.{miss}")

    # ไม่ใส่สถิติน้ำท่วมจากดาวเทียม GISTDA ในข้อความ: ภาพดาวเทียมไม่เรียลไทม์ อาจทำให้เข้าใจผิด

    # พยากรณ์ 24 ชม. ข้างหน้า (รายชั่วโมง) + 3 วันถัดไป
    nw = next24_text(summary.get("nwp_next24"))
    if nw:
        lines.append(f"⏱ คาดการณ์ฝน 24 ชม. ข้างหน้า: {nw} (กรมอุตุฯ)")
    fc = forecast_days(tmd)
    if fc:
        lines.append("📅 พยากรณ์ฝน (กรมอุตุฯ): " + " · ".join(f"{d} {r:.0f}มม." for d, r in fc))
    page = os.environ.get("PAGE_URL")
    if page:
        lines.append(f'\n<a href="{esc(page)}">เปิดหน้ารายงาน</a>')
    lines.append(f"<i>{now_th().strftime('%d/%m/%Y %H:%M')} น.</i>")
    return "\n".join(lines)


def next24_text(nw: dict | None) -> str | None:
    """ช่วงเวลาฝนตก 24 ชม. ข้างหน้าจาก NWP รายชั่วโมง"""
    if not nw:
        return None
    if not nw.get("start"):
        return "ไม่มีฝนนัยสำคัญ"
    today = now_th().date().isoformat()

    def hhmm(t, end=False):
        dt = datetime.fromisoformat(t) + (timedelta(hours=1) if end else timedelta())
        return ("พรุ่งนี้ " if dt.date().isoformat() != today else "") + dt.strftime("%H:%M")
    return f"{hhmm(nw['start'])}–{hhmm(nw['end'], True)} น. รวม ~{nw['total']:.0f} มม."


def forecast_days(tmd: dict) -> list:
    """พยากรณ์ฝนรายวัน 3 วันถัดไป → [("21/10", มม.), ...]"""
    today = now_th().date().isoformat()
    fc = [d for d in (tmd.get("forecast") or []) if d["date"] > today]
    return [(f"{int(d['date'][8:])}/{int(d['date'][5:7])}", d["rain"] or 0) for d in fc[:3]]


# ================================================================ LINE Flex
# สีป้ายระดับสถานการณ์ (พื้น, ตัวอักษร) ตาม LEVELS
FLEX_LEVEL = [("#dcfce7", "#166534"), ("#fef3c7", "#854d0e"), ("#ffedd5", "#9a3412"), ("#fee2e2", "#991b1b")]
FLEX_ALERT = "#b45309"          # สีตัวเลขที่ถึงเกณฑ์เฝ้าระวัง


def flex_row(label: str, value: str, sub: str | None = None, alert: bool = False) -> dict:
    row = {"type": "box", "layout": "horizontal", "spacing": "md", "contents": [
        {"type": "text", "text": label, "size": "sm", "color": "#666666", "flex": 5, "wrap": True},
        {"type": "text", "text": value, "size": "sm", "weight": "bold", "align": "end", "flex": 4,
         "wrap": True, "color": FLEX_ALERT if alert else "#111111"}]}
    if not sub:
        return row
    return {"type": "box", "layout": "vertical", "contents": [
        row, {"type": "text", "text": sub, "size": "xxs", "color": "#999999", "align": "end", "wrap": True}]}


def build_flex(summary: dict, tmd: dict, header: str) -> dict:
    """การ์ด LINE Flex — ข้อมูลชุดเดียวกับ build_message จัดเป็นตาราง ชื่อรายการ/ค่า"""
    lvl = summary["level"]
    bg, fg = FLEX_LEVEL[lvl]
    tw = summary.get("thaiwater") or {}
    groups = []

    # ฝน 24 ชม. / แรงสุดรายชั่วโมง / สะสม
    rows = []
    b = tw.get("max_in_district") or tw.get("max_nearby")
    if b:
        rows.append(flex_row("ฝน 24 ชม. สูงสุด", f"{b['rain_24h']} มม.", f"{b['name']} {place_label(b)}",
                             (b["rain_24h"] or 0) >= RAIN_HEAVY))
    i = tw.get("max_1h_in_district") or tw.get("max_1h_nearby")
    if i and (i.get("rain_1h") or 0) > 0:
        rows.append(flex_row("ฝนแรงสุดชั่วโมงล่าสุด", f"{i['rain_1h']} มม./ชม.", f"{i['name']} {place_label(i)}",
                             i["rain_1h"] >= RAIN_1H_INTENSE))
    rh = summary.get("rain_history") or {}
    if rh.get("sum7") is not None:
        miss = f" (ขาดข้อมูล {rh['missing7']} วัน)" if rh.get("missing7") else ""
        rows.append(flex_row("ฝนสะสม 3 วัน", f"{rh['sum3']:,.0f} มม."))
        rows.append(flex_row("ฝนสะสม 7 วัน", f"{rh['sum7']:,.0f} มม.", f"{rh['station']}{miss}",
                             rh["sum7"] >= RAIN7_SATURATED))
    groups.append(rows)

    # ระดับน้ำ 3 สถานีที่สูงที่สุด
    groups.append([flex_row(f"ระดับน้ำ {r['name']}", f"{r['pct']:.0f}% ตลิ่ง", place_label(r), r["pct"] >= WL_WATCH)
                   for r in (summary.get("waterlevel") or [])[:3]])

    # อ.เขาพนม จ.กระบี่: ฝนสูงสุด + อ่างเก็บน้ำ
    rows = []
    k = (tw.get("khaophanom") or {}).get("max_24h")
    if k and k.get("rain_24h") is not None:
        rows.append(flex_row(f"ฝนสูงสุด อ.{KP_AMPHOE}", f"{k['rain_24h']} มม.", f"{k['name']} ต.{k['tambon']}",
                             k["rain_24h"] >= RAIN_HEAVY))
    rows += [flex_row(d["name"].replace("อ่างเก็บน้ำ", "อ่างฯ "), f"{d['pct']:.0f}%")
             for d in summary.get("kp_dams") or []]
    groups.append(rows)

    # พยากรณ์ 24 ชม. ข้างหน้า + 3 วันถัดไป (กรมอุตุฯ)
    rows = []
    nw = next24_text(summary.get("nwp_next24"))
    if nw:
        rows.append(flex_row("คาดการณ์ฝน 24 ชม.", nw))
    rows += [flex_row(f"พยากรณ์ฝน {d}", f"{r:.0f} มม.") for d, r in forecast_days(tmd)]
    groups.append(rows)

    table = []
    for rows in (g for g in groups if g):
        if table:
            table.append({"type": "separator", "margin": "md", "color": "#e2e2e2"})
        table.append({"type": "box", "layout": "vertical", "spacing": "xs", "margin": "md", "contents": rows})

    body = [
        {"type": "box", "layout": "horizontal", "justifyContent": "center", "contents": [
            {"type": "box", "layout": "vertical", "width": "72px", "height": "72px", "cornerRadius": "36px",
             "backgroundColor": "#e8f0fb", "justifyContent": "center", "alignItems": "center",
             "contents": [{"type": "text", "text": "🌧️", "size": "3xl", "align": "center"}]}]},
        {"type": "text", "text": header, "weight": "bold", "size": "md", "align": "center", "wrap": True,
         "margin": "lg"},
        {"type": "text", "text": now_th().strftime("ในวันที่ %d/%m/%Y เวลา %H:%M น."), "size": "xs",
         "color": "#8a8a8a", "align": "center", "margin": "sm"},
        {"type": "text", "text": f"อ.{AMPHOE_TH} จ.{PROVINCE_TH}", "size": "sm", "color": "#555555",
         "align": "center", "margin": "xs"},
        {"type": "box", "layout": "horizontal", "justifyContent": "center", "margin": "md", "contents": [
            {"type": "box", "layout": "vertical", "flex": 0, "backgroundColor": bg, "cornerRadius": "20px",
             "paddingTop": "4px", "paddingBottom": "4px", "paddingStart": "16px", "paddingEnd": "16px",
             "contents": [{"type": "text", "text": f"● ระดับ: {LEVELS[lvl]['label']}", "size": "sm",
                           "weight": "bold", "color": fg}]}]},
    ]
    if table:
        body.append({"type": "box", "layout": "vertical", "margin": "lg", "backgroundColor": "#f4f4f4",
                     "cornerRadius": "12px", "paddingAll": "12px", "paddingTop": "2px", "contents": table})
    if summary["reasons"]:
        body.append({"type": "box", "layout": "vertical", "margin": "lg", "spacing": "xs", "contents": [
            {"type": "text", "text": "ข้อสังเกต", "size": "sm", "weight": "bold"},
            *[{"type": "text", "text": f"• {r['text']}", "size": "xs", "color": "#444444", "wrap": True}
              for r in summary["reasons"][:5]]]})

    bubble = {"type": "bubble", "size": "mega",
              "body": {"type": "box", "layout": "vertical", "paddingAll": "20px", "contents": body}}
    page = os.environ.get("PAGE_URL")
    if page:
        bubble["footer"] = {"type": "box", "layout": "vertical", "paddingAll": "20px", "paddingTop": "0px",
                            "contents": [{"type": "button", "style": "primary", "color": "#0b66cc", "height": "md",
                                          "action": {"type": "uri", "label": "เปิดหน้ารายงาน", "uri": page}}]}
    return {"type": "flex", "altText": f"{header} — อ.{AMPHOE_TH} ระดับ: {LEVELS[lvl]['label']}"[:400],
            "contents": bubble}


# ================================================================ main
def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", default="data", help="โฟลเดอร์ผลลัพธ์ (ค่าเริ่มต้น data)")
    ap.add_argument("--prev-url", default=os.environ.get("PREV_DATA_URL"),
                    help="URL โฟลเดอร์ data ของหน้าเว็บที่เผยแพร่อยู่ (ใช้เป็นข้อมูลรอบก่อน)")
    ap.add_argument("--no-telegram", action="store_true")
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)

    prev_summary = load_prev("summary.json", args.out, args.prev_url) or {}
    key = os.environ.get("GISTDA_API_KEY", "").strip()

    flood, fmap = fetch_gistda(key, args.out, args.prev_url)
    freq = fetch_flood_freq(key, args.out, args.prev_url)
    tmd = fetch_tmd(args.out, args.prev_url)
    try:
        tw = fetch_thaiwater_rain()
    except Exception as e:                              # noqa: BLE001
        log(f"ThaiWater ล้มเหลว: {e}")
        tw = None
    try:
        wl = fetch_waterlevel()
        log(f"ระดับน้ำ: {len(wl)} สถานี" + (f", สูงสุด {wl[0]['name']} {wl[0]['pct']}%" if wl else ""))
    except Exception as e:                              # noqa: BLE001
        log(f"ThaiWater ระดับน้ำ ล้มเหลว: {e}")
        wl = None
    try:
        rh = fetch_rain_history()
        log(f"ฝนสะสม {rh['station']}: 7 วัน {rh['sum7']} มม., 30 วัน {rh['sum30']} มม.")
    except Exception as e:                              # noqa: BLE001
        log(f"ThaiWater ฝนสะสม ล้มเหลว: {e}")
        rh = None
    try:
        kp_dams = fetch_kp_dams()
        log("อ่างเก็บน้ำ อ.เขาพนม: " + (", ".join(f"{d['name']} {d['pct']}%" for d in kp_dams) or "ไม่มีข้อมูล"))
    except Exception as e:                              # noqa: BLE001
        log(f"ThaiWater อ่างเก็บน้ำ ล้มเหลว: {e}")
        kp_dams = None
    nwin = nwp_rain_window(tmd.get("hourly"))

    level, reasons = assess(flood, tmd, tw, wl, rh, nwin, kp_dams)
    summary = {
        "generated_at": iso(now_th()),
        "area": {"amphoe": AMPHOE_TH, "province": PROVINCE_TH, "lat": LAT, "lon": LON, "amphoe_code": AMPHOE_CODE},
        **LEVELS[level],
        "reasons": reasons,
        "thaiwater": tw,
        "waterlevel": wl,
        "rain_history": {k: v for k, v in rh.items() if k != "days"} if rh else None,
        "nwp_next24": nwin,
        "kp_dams": kp_dams,
        "sources": {
            "gistda": "error" not in flood or bool(flood.get("periods")),
            "gistda_stale": bool(flood.get("stale")),
            "tmd_obs": bool(tmd.get("obs3h")),
            "tmd_warnings": "warnings" in tmd,
            "tmd_forecast": bool(tmd.get("forecast")),
            "thaiwater": tw is not None,
            "waterlevel": bool(wl),
            "rain_history": rh is not None,
        },
        "warning_titles": [w["title"] for w in (tmd.get("warnings") or []) if w.get("relevant")],
    }

    write_json(os.path.join(args.out, "flood.json"), flood)
    write_json(os.path.join(args.out, "flood_map.json"), fmap)
    if freq:
        write_json(os.path.join(args.out, "flood_freq.json"), freq)
    write_json(os.path.join(args.out, "tmd.json"), tmd)
    write_json(os.path.join(args.out, "summary.json"), summary)
    log(f"ระดับ: {summary['label']} ({level}) — {len(reasons)} เหตุผล")

    # ---- แจ้งเตือน Telegram / LINE หมอพร้อม
    if args.no_telegram:
        return
    daily = os.environ.get("DAILY_REPORT", "").lower() in ("1", "true", "yes")
    prev_level = prev_summary.get("level")
    new_warn = [t for t in summary["warning_titles"] if t not in (prev_summary.get("warning_titles") or [])]
    head = None
    if daily:
        head = "รายงานสถานการณ์ฝน/น้ำท่วมประจำวัน"
    elif prev_level is not None and level != prev_level:
        head = "⚠️ ระดับสถานการณ์สูงขึ้น" if level > prev_level else "ℹ️ ระดับสถานการณ์ลดลง"
    elif prev_summary and new_warn:
        head = "📢 กรมอุตุฯ ออกประกาศเตือนภัยใหม่"
    if head:
        notify(build_message(summary, flood, tmd, head), build_flex(summary, tmd, head))


if __name__ == "__main__":
    main()
