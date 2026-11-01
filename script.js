"use strict";

const $  = (s, r = document) => r.querySelector(s);
const $$ = (s, r = document) => Array.from(r.querySelectorAll(s));
const esc = s => String(s).replace(/[&<>"']/g, c =>
  ({ "&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;" }[c]));

function showView(name){
  $$(".nav-btn").forEach(b => b.classList.toggle("active", b.dataset.view === name));
  $$(".view").forEach(v => v.classList.toggle("active", v.id === "view-" + name));
  window.scrollTo({ top: 0, behavior: "smooth" });
}
function initNav(){
  $$(".nav-btn").forEach(b => b.addEventListener("click", () => showView(b.dataset.view)));
  $$("[data-goto]").forEach(b => b.addEventListener("click", () => showView(b.dataset.goto)));
}

/* ==================================================================
   1 · QUINE–McCLUSKEY
   ================================================================== */
function cubeMinterms(bits, mask, nVars){
  const free = [];
  for (let i = 0; i < nVars; i++){
    const b = 1 << (nVars - 1 - i);
    if (mask & b) free.push(i);
  }
  const total = 1 << free.length;
  const out = [];
  for (let v = 0; v < total; v++){
    let m = bits;
    for (let k = 0; k < free.length; k++){
      const b = 1 << (nVars - 1 - free[k]);
      if ((v >> k) & 1) m |= b; else m &= ~b;
    }
    out.push(m);
  }
  return out;
}

function quineMcCluskey(minterms, nVars){
  const total = 1 << nVars;
  if (!minterms.length) return [];
  if (minterms.length === total)
    return [{ bits: 0, mask: total - 1, cover: new Set(minterms) }];
  let current = minterms.slice().sort((a,b)=>a-b)
    .map(m => ({ bits: m, mask: 0, cover: new Set([m]) }));
  const primes = [];
  while (current.length){
    const used = new Array(current.length).fill(false);
    const nextMap = new Map();
    for (let i = 0; i < current.length; i++){
      for (let j = i+1; j < current.length; j++){
        const a = current[i], b = current[j];
        if (a.mask !== b.mask) continue;
        const diff = a.bits ^ b.bits;
        if (diff === 0 || (diff & (diff-1)) !== 0) continue;
        used[i] = used[j] = true;
        const nb = a.bits & ~diff;
        const nm = a.mask | diff;
        const key = nb + ":" + nm;
        if (!nextMap.has(key)){
          nextMap.set(key, { bits: nb, mask: nm,
            cover: new Set([...a.cover, ...b.cover]) });
        } else {
          const t = nextMap.get(key);
          for (const c of a.cover) t.cover.add(c);
          for (const c of b.cover) t.cover.add(c);
        }
      }
    }
    for (let i = 0; i < current.length; i++) if (!used[i]) primes.push(current[i]);
    current = [...nextMap.values()];
  }
  const seen = new Set();
  const uniq = [];
  for (const p of primes){
    const k = p.bits + ":" + p.mask;
    if (seen.has(k)) continue;
    seen.add(k); uniq.push(p);
  }
  return uniq;
}

function coverMinterms(primes, minterms){
  const chosen = [];
  const chosenKeys = new Set();
  const remaining = new Set(minterms);
  for (const m of minterms){
    const cov = primes.filter(p => p.cover.has(m));
    if (cov.length === 1){
      const p = cov[0];
      const k = p.bits + ":" + p.mask;
      if (!chosenKeys.has(k)){ chosenKeys.add(k); chosen.push(p); }
    }
  }
  for (const p of chosen) for (const m of p.cover) remaining.delete(m);
  let guard = 0;
  while (remaining.size && guard++ < 64){
    let best = null, bestCount = 0;
    for (const p of primes){
      const k = p.bits + ":" + p.mask;
      if (chosenKeys.has(k)) continue;
      let cnt = 0;
      for (const m of p.cover) if (remaining.has(m)) cnt++;
      if (cnt > bestCount){ best = p; bestCount = cnt; }
    }
    if (!best || bestCount === 0) break;
    chosenKeys.add(best.bits + ":" + best.mask);
    chosen.push(best);
    for (const m of best.cover) remaining.delete(m);
  }
  return chosen;
}

function optimizePLA(functions, nVars){
  const candidates = [];
  const byKey = new Map();
  functions.forEach((f, fi) => {
    if (!f.minterms.length) return;
    const primes = quineMcCluskey(f.minterms, nVars);
    const fset = new Set(f.minterms);
    for (const p of primes){
      const k = p.bits + ":" + p.mask;
      let entry = byKey.get(k);
      if (!entry){
        entry = {
          bits: p.bits, mask: p.mask,
          subcube: cubeMinterms(p.bits, p.mask, nVars),
          covers: new Map()
        };
        byKey.set(k, entry);
        candidates.push(entry);
      }
      const allIn = entry.subcube.every(m => fset.has(m));
      if (allIn){
        const set = new Set();
        for (const m of entry.subcube) if (fset.has(m)) set.add(m);
        entry.covers.set(fi, set);
      }
    }
  });
  const targets = new Set();
  functions.forEach((f, fi) => f.minterms.forEach(m => targets.add(fi + ":" + m)));
  const uncovered = new Set(targets);
  const selected = [];
  while (uncovered.size){
    let best = null, bestCount = 0;
    for (const c of candidates){
      let cnt = 0;
      for (const [fi, mins] of c.covers){
        for (const m of mins) if (uncovered.has(fi + ":" + m)) cnt++;
      }
      if (cnt > bestCount){ best = c; bestCount = cnt; }
    }
    if (!best || bestCount === 0) break;
    selected.push(best);
    for (const [fi, mins] of best.covers){
      for (const m of mins) uncovered.delete(fi + ":" + m);
    }
  }
  return selected;
}

const VAR_NAMES = ["A","B","C","D","E"];

function termString(term, nVars){
  const parts = [];
  for (let i = 0; i < nVars; i++){
    const b = 1 << (nVars - 1 - i);
    if (term.mask & b) continue;
    // Use single quote for negation
    parts.push((term.bits & b) ? VAR_NAMES[i] : VAR_NAMES[i] + "'");
  }
  return parts.length ? parts.join("·") : "1";
}
function sopString(cover, nVars){
  if (!cover.length) return "0";
  return cover.map(p => termString(p, nVars)).join("  +  ");
}
function mintermList(minterms){
  return minterms.length ? `Σm(${minterms.join(",")})` : "-";
}

/* ==================================================================
   2 · PLD DESIGNER
   ================================================================== */
const pldState = {
  nVars: 3,
  functions: [
    { name: "F1", minterms: [1,4,5] },
    { name: "F2", minterms: [1,3,5] }
  ]
};

function pldRenderVarNames(){
  $("#pldVarNames").textContent = VAR_NAMES.slice(0, pldState.nVars).join(" · ");
}

function pldRenderFunctions(){
  const box = $("#pldFuncList");
  box.innerHTML = "";
  pldState.functions.forEach((f, i) => {
    const row = document.createElement("div");
    row.className = "func-row";
    row.innerHTML = `
      <input class="func-name" value="${esc(f.name)}" spellcheck="false">
      <input class="func-mins" value="${esc(f.minterms.join(","))}" spellcheck="false"
             placeholder="e.g. 1,2,3,6,9,11">
      <button class="icon-btn del" title="Remove">×</button>`;
    row.querySelector(".func-name").addEventListener("input", e => {
      pldState.functions[i].name = e.target.value;
    });
    row.querySelector(".func-mins").addEventListener("input", e => {
      pldState.functions[i].minterms = parseMinterms(e.target.value, (1<<pldState.nVars)-1);
    });
    row.querySelector(".del").addEventListener("click", () => {
      if (pldState.functions.length <= 1) return;
      pldState.functions.splice(i, 1);
      pldRenderFunctions();
    });
    box.appendChild(row);
  });
}

function parseMinterms(str, maxM){
  const s = String(str).replace(/[Σσ]/g, "").replace(/[mM]\s*\(/g, "(");
  const nums = s.match(/\d+/g) || [];
  const seen = new Set();
  const out = [];
  for (const n of nums){
    const v = parseInt(n, 10);
    if (Number.isFinite(v) && v >= 0 && v <= maxM && !seen.has(v)){
      seen.add(v); out.push(v);
    }
  }
  return out.sort((a,b)=>a-b);
}

function renderTruthTable(nVars, functions, rows){
  const el = $("#pldTruth");
  if (!rows.length){
    el.innerHTML = '<div class="empty">No data — check the minterm lists.</div>';
    return;
  }
  let html = '<table class="tt"><thead><tr><th class="idx">#</th>';
  for (let i = 0; i < nVars; i++) html += `<th>${VAR_NAMES[i]}</th>`;
  for (const f of functions) html += `<th class="out">${esc(f.name)}</th>`;
  html += "</tr></thead><tbody>";
  for (const r of rows){
    html += `<tr><td class="idx">${r.m}</td>`;
    for (let i = 0; i < nVars; i++){
      const v = (r.m >> (nVars-1-i)) & 1;
      html += `<td class="${v ? "one" : "zero"}">${v}</td>`;
    }
    for (const v of r.out) html += `<td class="${v ? "one" : "zero"}">${v}</td>`;
    html += "</tr>";
  }
  html += "</tbody></table>";
  el.innerHTML = html;
}

function grayCode(k){
  if (k === 0) return [0];
  const out = [];
  for (let i = 0; i < (1<<k); i++) out.push(i ^ (i>>1));
  return out;
}

function renderKmap(title, nVars, values){
  const layout = { 1:[1,0], 2:[1,1], 3:[1,2], 4:[2,2] };
  const [rv, cv] = layout[nVars] || [2,2];
  const rowLabels = grayCode(rv);
  const colLabels = grayCode(cv);
  const rowVars = VAR_NAMES.slice(0, rv).join("");
  const colVars = VAR_NAMES.slice(rv, rv+cv).join("");
  const bitLabel = (v, bits) => {
    let s = "";
    for (let i = bits-1; i >= 0; i--) s += ((v >> i) & 1);
    return s || "'";
  };
  let html = `<div class="kmap-block"><div class="kmap-label">${esc(title)}</div>`;
  html += '<table class="kmap"><thead><tr>';
  html += `<th class="corner">${esc(rowVars||"·")} \\ ${esc(colVars||"·")}</th>`;
  for (const c of colLabels) html += `<th>${bitLabel(c, cv)}</th>`;
  html += "</tr></thead><tbody>";
  for (const r of rowLabels){
    html += `<tr><th>${bitLabel(r, rv)}</th>`;
    for (const c of colLabels){
      let m = 0;
      for (let i = 0; i < rv; i++) m |= ((r >> (rv-1-i)) & 1) << (nVars-1-i);
      for (let i = 0; i < cv; i++) m |= ((c >> (cv-1-i)) & 1) << (nVars-1-rv-i);
      const v = values[m] ? 1 : 0;
      html += `<td class="${v ? "one" : ""}">${v}</td>`;
    }
    html += "</tr>";
  }
  html += "</tbody></table></div>";
  return html;
}

function renderPLATable(nVars, functions, terms, mode){
  const el = $("#pldTable");
  if (!terms.length){
    el.innerHTML = '<div class="empty">No product terms to display.</div>';
    return;
  }
  let html = '<table class="tt"><thead><tr>';
  html += '<th>Sr.</th><th>Product term</th>';
  for (let i = 0; i < nVars; i++) html += `<th>${VAR_NAMES[i]}</th>`;
  
  if (mode === "pal") {
    html += '<th class="out">Target Output</th>';
  } else {
    for (const f of functions) html += `<th class="out">${esc(f.name)}</th>`;
  }
  html += "</tr></thead><tbody>";
  
  terms.forEach((t, i) => {
    html += `<tr><td class="idx">${i+1}</td>`;
    html += `<td class="term">${esc(termString(t, nVars))}</td>`;
    for (let k = 0; k < nVars; k++){
      const b = 1 << (nVars-1-k);
      if (t.mask & b) html += `<td class="minus">–</td>`;
      else html += `<td class="${t.bits & b ? "one" : "zero"}">${t.bits & b ? 1 : 0}</td>`;
    }
    
    if (mode === "pal") {
      html += `<td class="one">${esc(functions[t.output].name)}</td>`;
    } else {
      for (let fi = 0; fi < functions.length; fi++){
        if (mode === "prom") {
          // PROM checks if the minterm is part of the function
          html += functions[fi].minterms.includes(t.bits) ? `<td class="one">1</td>` : `<td class="minus">–</td>`;
        } else {
          // PLA checks if the term covers the output
          html += t.covers.has(fi) ? `<td class="one">1</td>` : `<td class="minus">–</td>`;
        }
      }
    }
    html += "</tr>";
  });
  html += "</tbody></table>";
  el.innerHTML = html;
}

/* ==================================================================
   ★★★★★  PLA CIRCUIT — Multi-Mode  ★★★★★
   ================================================================== */
function renderPLACircuit(nVars, functions, terms, mode){
  const el = $("#pldCircuit");
  if (!terms.length){
    el.innerHTML = '<div class="empty">No circuit to draw.</div>';
    return;
  }

  const nLines = nVars * 2;
  const nTerms = terms.length;
  const nOut   = functions.length;

  /* ---------- horizontal geometry ---------- */
  const padL = 90;
  const lineGap  = 26;
  const termGap  = 80;
  const andGateW = 44, andGateH = 34;
  const orGap    = 42;

  const x0 = padL + 90;
  const termX = j => x0 + j * termGap;
  const railStart = 30;
  const orGateX = termX(nTerms - 1) + 60;

  /* ---------- vertical geometry with banner bands ---------- */
  const padT = 50;
  const lineY = i => padT + i * lineGap;
  const lastRailY = lineY(nLines - 1);

  // AND PLANE banner band
  const AND_BANNER_H   = 34;
  const AND_BANNER_TOP = lastRailY + 28;
  const AND_BANNER_BOT = AND_BANNER_TOP + AND_BANNER_H;

  const VERTICAL_RESUME_Y = AND_BANNER_BOT + 22;

  // AND gates
  const AND_GATE_TOP    = VERTICAL_RESUME_Y + 60;
  const AND_GATE_BOT    = AND_GATE_TOP + andGateH;
  const AND_OUT_LABEL_Y = AND_GATE_BOT + 22;

  // OR PLANE banner band
  const OR_BANNER_H   = 34;
  const OR_BANNER_TOP = AND_OUT_LABEL_Y + 28;
  const OR_BANNER_BOT = OR_BANNER_TOP + OR_BANNER_H;

  // OR lines resume below the banner
  const OR_LINE_Y0 = OR_BANNER_BOT + 30;
  const orY = k => OR_LINE_Y0 + k * orGap;

  /* ---------- overall canvas ---------- */
  const svgW = orGateX + 260;
  const svgH = orY(nOut - 1) + 80;
  const railEnd = svgW - 40;

  const parts = [];
  parts.push(`<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${svgW} ${svgH}"
                  width="${svgW}" height="${svgH}"
                  font-family="JetBrains Mono,monospace">`);
  parts.push(`<defs>
    <marker id="arr" viewBox="0 0 10 10" refX="9" refY="5"
            markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M0,0 L10,5 L0,10 z" fill="#e2b968"/>
    </marker>
  </defs>`);

  /* =========================================================
     SECTION 1 — INPUT BUFFERS
     ========================================================= */
  parts.push(`<text x="14" y="20" font-size="11" font-weight="700"
                    letter-spacing="3" fill="#8fb0d0">INPUT BUFFERS</text>`);

  for (let i = 0; i < nLines; i++){
    const y = lineY(i);
    parts.push(`<line x1="${railStart}" y1="${y}" x2="${railEnd}" y2="${y}"
                       stroke="#3a5573" stroke-width="1"/>`);
    const varIdx = Math.floor(i / 2);
    const isComp = i % 2 === 1;
    // Use single quote for negation in labels
    const label = isComp ? VAR_NAMES[varIdx] + "'" : VAR_NAMES[varIdx];
    parts.push(`<text x="${railStart - 6}" y="${y + 4}" text-anchor="end"
                       font-size="12" font-weight="700" fill="#e2b968">${label}</text>`);
  }
  for (let v = 0; v < nVars; v++){
    const yTrue = lineY(v*2);
    const yComp = lineY(v*2 + 1);
    const bx = padL - 14;
    parts.push(`<polygon points="${bx},${yTrue-8} ${bx},${yComp+8} ${bx+16},${(yTrue+yComp)/2}"
                        fill="none" stroke="#4fd1e6" stroke-width="1.3"/>`);
  }

  /* =========================================================
     SECTION 2a — PRODUCT-TERM VERTICALS (TOP SEGMENT)
     ========================================================= */
  for (let j = 0; j < nTerms; j++){
    const x = termX(j);
    parts.push(`<line x1="${x}" y1="${lineY(0) - 4}" x2="${x}" y2="${AND_BANNER_TOP}"
                       stroke="#4fd1e6" stroke-width="1.1" opacity="0.75"/>`);
    
    // PROM has a fixed decoder (no programmable dots)
    if (mode !== "prom") {
      for (let i = 0; i < nLines; i++){
        const varIdx = Math.floor(i / 2);
        const isComp = i % 2 === 1;
        const b = 1 << (nVars-1-varIdx);
        let uses = false;
        if (!(terms[j].mask & b)){
          const want = (terms[j].bits & b) ? 0 : 1;
          if (want === (isComp ? 1 : 0)) uses = true;
        }
        if (uses){
          parts.push(`<circle cx="${x}" cy="${lineY(i)}" r="3.4" fill="#e2b968"/>`);
        }
      }
    }
  }

  /* =========================================================
     AND PLANE BANNER
     ========================================================= */
  const andBannerLeft  = termX(0) - 40;
  const andBannerRight = termX(nTerms - 1) + 40;
  parts.push(`<line x1="${andBannerLeft}" y1="${AND_BANNER_TOP}"
                    x2="${andBannerRight}" y2="${AND_BANNER_TOP}"
                    stroke="rgba(74,222,128,0.55)" stroke-width="1.2"
                    stroke-dasharray="6 5"/>`);
  parts.push(`<line x1="${andBannerLeft}" y1="${AND_BANNER_BOT}"
                    x2="${andBannerRight}" y2="${AND_BANNER_BOT}"
                    stroke="rgba(74,222,128,0.55)" stroke-width="1.2"
                    stroke-dasharray="6 5"/>`);
  const andBannerText = mode === "prom" ? "FIXED AND ARRAY (DECODER)" : "AND PLANE";
  parts.push(`<text x="${(andBannerLeft + andBannerRight) / 2}"
                    y="${AND_BANNER_TOP + AND_BANNER_H/2 + 5}"
                    text-anchor="middle" font-size="12" font-weight="800"
                    letter-spacing="5" fill="#4ade80">${andBannerText}</text>`);

  /* =========================================================
     SECTION 2b — PRODUCT-TERM VERTICALS (BOTTOM SEGMENT)
     ========================================================= */
  for (let j = 0; j < nTerms; j++){
    const x = termX(j);
    parts.push(`<line x1="${x}" y1="${AND_BANNER_BOT}" x2="${x}" y2="${AND_GATE_TOP}"
                       stroke="#4fd1e6" stroke-width="1.1" opacity="0.75"/>`);
  }

  /* =========================================================
     AND GATES + product-term name labels
     ========================================================= */
  for (let j = 0; j < nTerms; j++){
    const cx = termX(j);
    const y  = AND_GATE_TOP;
    const xL = cx - andGateW/2;
    
    // Color-code AND gates by output in PAL mode to show fixed OR
    const gateColor = mode === "pal" ? `hsl(${terms[j].output * 137.5}, 70%, 60%)` : "#4ade80";
    
    parts.push(`<path d="M ${xL} ${y} L ${cx} ${y}
                        A ${andGateW/2} ${andGateH/2} 0 0 1 ${cx} ${y + andGateH}
                        L ${xL} ${y + andGateH} Z"
                       fill="rgba(74,222,128,0.08)" stroke="${gateColor}" stroke-width="1.4"/>`);
    parts.push(`<text x="${cx}" y="${AND_OUT_LABEL_Y}" text-anchor="middle"
                       font-size="11" fill="${gateColor}" font-weight="700">${esc(termString(terms[j], nVars))}</text>`);
  }

  /* =========================================================
     SECTION 3a — AND-GATE OUTPUT VERTICALS (TOP SEGMENT)
     ========================================================= */
  for (let j = 0; j < nTerms; j++){
    const cx = termX(j);
    parts.push(`<line x1="${cx}" y1="${AND_GATE_BOT}" x2="${cx}" y2="${OR_BANNER_TOP}"
                       stroke="#4ade80" stroke-width="1.1" opacity="0.65"/>`);
  }

  /* =========================================================
     OR PLANE BANNER
     ========================================================= */
  const orBannerLeft  = termX(0) - 40;
  const orBannerRight = orGateX + 60;
  parts.push(`<line x1="${orBannerLeft}" y1="${OR_BANNER_TOP}"
                    x2="${orBannerRight}" y2="${OR_BANNER_TOP}"
                    stroke="rgba(91,141,239,0.55)" stroke-width="1.2"
                    stroke-dasharray="6 5"/>`);
  parts.push(`<line x1="${orBannerLeft}" y1="${OR_BANNER_BOT}"
                    x2="${orBannerRight}" y2="${OR_BANNER_BOT}"
                    stroke="rgba(91,141,239,0.55)" stroke-width="1.2"
                    stroke-dasharray="6 5"/>`);
  const orBannerText = mode === "pal" ? "FIXED OR ARRAY" : "OR PLANE";
  parts.push(`<text x="${(orBannerLeft + orBannerRight) / 2}"
                    y="${OR_BANNER_TOP + OR_BANNER_H/2 + 5}"
                    text-anchor="middle" font-size="12" font-weight="800"
                    letter-spacing="5" fill="#5b8def">${orBannerText}</text>`);

  /* =========================================================
     SECTION 3b — AND-GATE OUTPUT VERTICALS (BOTTOM SEGMENT)
     ========================================================= */
  for (let j = 0; j < nTerms; j++){
    const cx = termX(j);
    parts.push(`<line x1="${cx}" y1="${OR_BANNER_BOT}" x2="${cx}" y2="${orY(nOut-1)}"
                       stroke="#4ade80" stroke-width="1.1" opacity="0.65"/>`);
  }

  /* =========================================================
     OR LINES + cross-points + shield OR gates + LONG output arrows
     ========================================================= */
  const arrowStart = orGateX + 46;
  const arrowEnd   = arrowStart + 120;
  const labelX     = arrowEnd + 14;

  for (let k = 0; k < nOut; k++){
    const y = orY(k);
    parts.push(`<line x1="${termX(0) - 20}" y1="${y}" x2="${orGateX}" y2="${y}"
                       stroke="#5b8def" stroke-width="1.2"/>`);
                       
    for (let j = 0; j < nTerms; j++){
      if (mode === "pal") {
        // PAL: Fixed OR connections (only to the designated output)
        if (terms[j].output === k) {
          parts.push(`<circle cx="${termX(j)}" cy="${y}" r="3.4" fill="#e2b968"/>`);
        }
      } else if (mode === "prom") {
        // PROM: Programmable OR connections
        if (functions[k].minterms.includes(terms[j].bits)) {
          parts.push(`<circle cx="${termX(j)}" cy="${y}" r="3.4" fill="#e2b968"/>`);
        }
      } else {
        // PLA: Programmable OR connections
        if (terms[j].covers.has(k)) {
          parts.push(`<circle cx="${termX(j)}" cy="${y}" r="3.4" fill="#e2b968"/>`);
        }
      }
    }
    
    const gx = orGateX, gy = y - 12;
    parts.push(`<path d="M ${gx} ${gy} Q ${gx+34} ${gy} ${gx+46} ${gy+12}
                        Q ${gx+34} ${gy+24} ${gx} ${gy+24}
                        Q ${gx+14} ${gy+12} ${gx} ${gy} Z"
                       fill="rgba(91,141,239,0.1)" stroke="#5b8def" stroke-width="1.4"/>`);
    parts.push(`<line x1="${arrowStart}" y1="${y}" x2="${arrowEnd}" y2="${y}"
                       stroke="#e2b968" stroke-width="1.5" marker-end="url(#arr)"/>`);
    parts.push(`<text x="${labelX}" y="${y + 5}" text-anchor="start"
                       font-size="14" font-weight="800" fill="#e2b968">${esc(functions[k].name)}</text>`);
  }

  parts.push(`</svg>`);
  el.innerHTML = parts.join("");
}

function renderExpressions(nVars, functions, perFunctionCovers){
  const el = $("#pldExpressions");
  let html = "";
  functions.forEach((f, i) => {
    const cover = perFunctionCovers[i];
    const eq = cover.length ? sopString(cover, nVars) : "0";
    html += `<div class="expr-card">
      <div class="expr-name">${esc(f.name)}</div>
      <div class="expr-body">${esc(eq)}</div>
      <div class="expr-meta">${esc(mintermList(f.minterms))} · ${cover.length} product term${cover.length === 1 ? "" : "s"} in minimal cover</div>
    </div>`;
  });
  el.innerHTML = html;
}

function synthesizePLD(){
  const nVars = pldState.nVars;
  const mode = $("#pldType").value;
  const maxM = (1 << nVars) - 1;
  
  pldState.functions.forEach(f => {
    f.minterms = [...new Set(f.minterms)]
      .filter(m => m >= 0 && m <= maxM).sort((a,b)=>a-b);
  });

  let perFunctionCovers = [];
  let sharedTerms = [];

  if (mode === "pla") {
    perFunctionCovers = pldState.functions.map(f =>
      coverMinterms(quineMcCluskey(f.minterms, nVars), f.minterms));
    sharedTerms = optimizePLA(pldState.functions, nVars);
  } else if (mode === "pal") {
    // PAL: Minimize independently, fixed OR arrays (no sharing)
    perFunctionCovers = pldState.functions.map(f =>
      coverMinterms(quineMcCluskey(f.minterms, nVars), f.minterms));
    sharedTerms = [];
    pldState.functions.forEach((f, fi) => {
      perFunctionCovers[fi].forEach(term => {
        sharedTerms.push({ ...term, output: fi });
      });
    });
  } else if (mode === "prom") {
    // PROM: Fixed AND array (all minterms), programmable OR
    const total = 1 << nVars;
    sharedTerms = [];
    for (let m = 0; m < total; m++) {
      sharedTerms.push({ bits: m, mask: 0, cover: new Set([m]) });
    }
    perFunctionCovers = pldState.functions.map(f => {
      return f.minterms.map(m => ({ bits: m, mask: 0, cover: new Set([m]) }));
    });
  }

  const rows = [];
  const total = 1 << nVars;
  for (let m = 0; m < total; m++){
    const outs = pldState.functions.map(f => f.minterms.includes(m) ? 1 : 0);
    rows.push({ m, out: outs });
  }

  renderExpressions(nVars, pldState.functions, perFunctionCovers);
  renderTruthTable(nVars, pldState.functions, rows);

  let kmapHtml = "";
  pldState.functions.forEach(f => {
    const values = [];
    for (let m = 0; m < total; m++) values[m] = f.minterms.includes(m) ? 1 : 0;
    kmapHtml += renderKmap(f.name, nVars, values);
  });
  $("#pldKmap").innerHTML = kmapHtml;

  renderPLATable(nVars, pldState.functions, sharedTerms, mode);
  renderPLACircuit(nVars, pldState.functions, sharedTerms, mode);
}

function initPLD(){
  pldRenderVarNames();
  pldRenderFunctions();
  $$(".var-pill").forEach(p => p.addEventListener("click", () => {
    $$(".var-pill").forEach(x => x.classList.toggle("active", x === p));
    pldState.nVars = parseInt(p.dataset.n, 10);
    pldRenderVarNames();
    const maxM = (1 << pldState.nVars) - 1;
    pldState.functions.forEach(f => f.minterms = f.minterms.filter(m => m <= maxM));
    pldRenderFunctions();
  }));
  $("#pldAddFunc").addEventListener("click", () => {
    const idx = pldState.functions.length;
    pldState.functions.push({ name: "F" + (idx+1), minterms: [] });
    pldRenderFunctions();
  });
  $("#pldCompute").addEventListener("click", synthesizePLD);
  $("#pldType").addEventListener("change", synthesizePLD);
  $("#pldPreset").addEventListener("change", e => {
    const v = e.target.value;
    if (!v) return;
    applyPreset(v);
    e.target.value = "";
  });
}

function applyPreset(key){
  const presets = {
    "fulladder": { n: 3, functions: [
      { name: "S",    minterms: [1,2,4,7] },
      { name: "Cout", minterms: [3,5,6,7] }
    ]},
    "halfadder": { n: 2, functions: [
      { name: "S",    minterms: [1,2] },
      { name: "Cout", minterms: [3] }
    ]},
    "ex-3var": { n: 3, functions: [
      { name: "F1", minterms: [1,4,5] },
      { name: "F2", minterms: [1,3,5] }
    ]},
    "ex-4var": { n: 4, functions: [
      { name: "F1", minterms: [1,2,3,6,9,11] },
      { name: "F2", minterms: [0,1,2,6,8,9] },
      { name: "F3", minterms: [2,3,8,9,11] }
    ]},
    "ex-alt": { n: 3, functions: [
      { name: "F1", minterms: [0,2,5,7] },
      { name: "F2", minterms: [2,3,4,5] }
    ]},
    "gray2bin": { n: 3, functions: [
      { name: "B2", minterms: [1,2,5,6] },
      { name: "B1", minterms: [1,3,4,6] },
      { name: "B0", minterms: [1,4] }
    ]}
  };
  const p = presets[key];
  if (!p) return;
  pldState.nVars = p.n;
  pldState.functions = p.functions.map(f => ({ name: f.name, minterms: f.minterms.slice() }));
  $$(".var-pill").forEach(x => x.classList.toggle("active", parseInt(x.dataset.n,10) === p.n));
  pldRenderVarNames();
  pldRenderFunctions();
  synthesizePLD();
  showView("pld");
}

/* ==================================================================
   3 · ASM CHART BUILDER
   ================================================================== */
const asmState = { elements: [] };

const ASM_DEFAULTS = {
  state: { name: "S0", code: "00", ops: "M = 0" },
  decision: { condition: "X = 1?", trueLabel: "1", falseLabel: "0", loopFalse: true },
  conditional: { outputs: "Y = 1" }
};

function asmAdd(type){
  const el = { type, ...structuredClone(ASM_DEFAULTS[type]) };
  if (type === "state"){
    const n = asmState.elements.filter(e => e.type === "state").length;
    el.name = "S" + n;
    el.code = n.toString(2).padStart(2, "0");
  }
  asmState.elements.push(el);
  renderASM();
}
function asmRemove(i){ asmState.elements.splice(i, 1); renderASM(); }
function asmMove(i, d){
  const j = i + d;
  if (j < 0 || j >= asmState.elements.length) return;
  [asmState.elements[i], asmState.elements[j]] = [asmState.elements[j], asmState.elements[i]];
  renderASM();
}

function renderASMList(){
  const box = $("#asmList");
  box.innerHTML = "";
  $("#asmCount").textContent = asmState.elements.length;
  if (!asmState.elements.length){
    box.innerHTML = '<div class="empty" style="padding:14px 4px;">No elements yet. Use the buttons above or click Auto Generate.</div>';
    return;
  }
  asmState.elements.forEach((el, i) => {
    const card = document.createElement("div");
    card.className = "asm-card";
    card.dataset.type = el.type;
    if (el.type === "decision" && el.loopFalse) card.classList.add("loop-on");
    const title = { state: "State box", decision: "Decision box", conditional: "Conditional box" }[el.type];
    const loopBadge = (el.type === "decision" && el.loopFalse)
      ? '<span class="asm-loop-badge">↻ self-loop</span>' : "";
    card.innerHTML = `
      <div class="asm-card-head">
        <span class="asm-card-title">${i+1} · ${title} ${loopBadge}</span>
        <div class="asm-card-btns">
          <button class="icon-btn" data-act="up" title="Move up">↑</button>
          <button class="icon-btn" data-act="down" title="Move down">↓</button>
          <button class="icon-btn del" data-act="del" title="Delete">×</button>
        </div>
      </div>
      <div class="asm-fields"></div>`;
    const fields = card.querySelector(".asm-fields");
    const addInput = (label, key, val) => {
      const wrap = document.createElement("div");
      wrap.className = "asm-field";
      wrap.innerHTML = `<label>${label}</label><input value="${esc(val)}" spellcheck="false">`;
      wrap.querySelector("input").addEventListener("input", e => {
        el[key] = e.target.value; renderASMChart();
      });
      fields.appendChild(wrap);
    };
    const addTextarea = (label, key, val) => {
      const wrap = document.createElement("div");
      wrap.className = "asm-field";
      wrap.innerHTML = `<label>${label}</label><textarea spellcheck="false">${esc(val)}</textarea>`;
      wrap.querySelector("textarea").addEventListener("input", e => {
        el[key] = e.target.value; renderASMChart();
      });
      fields.appendChild(wrap);
    };
    const addToggle = (label, key, val, hintText) => {
      const wrap = document.createElement("div");
      wrap.className = "asm-field toggle-row";
      wrap.innerHTML = `<label>${label}</label>
        <input type="checkbox" class="asm-check" ${val ? "checked" : ""}>
        <span class="asm-check-label">${esc(hintText)}</span>`;
      wrap.querySelector("input").addEventListener("change", e => {
        el[key] = e.target.checked; renderASM();
      });
      fields.appendChild(wrap);
    };
    if (el.type === "state"){
      addInput("Name", "name", el.name);
      addInput("Code", "code", el.code);
      addTextarea("Ops", "ops", el.ops);
    } else if (el.type === "decision"){
      addInput("Cond", "condition", el.condition);
      addInput("True", "trueLabel", el.trueLabel);
      addInput("False", "falseLabel", el.falseLabel);
      addToggle("Loop", "loopFalse", el.loopFalse, "On false → return to current state");
    } else {
      addTextarea("Outputs", "outputs", el.outputs);
    }
    card.querySelectorAll("[data-act]").forEach(b => b.addEventListener("click", () => {
      const a = b.dataset.act;
      if (a === "del") asmRemove(i);
      else if (a === "up") asmMove(i, -1);
      else if (a === "down") asmMove(i, 1);
    }));
    box.appendChild(card);
  });
}

function renderASMChart(){
  const cv = $("#asmCanvas");
  const els = asmState.elements;
  if (!els.length){
    cv.innerHTML = '<div class="empty">Add elements on the left to build the ASM chart.</div>';
    return;
  }
  const W = 560, CX = W / 2;
  const stateH = 82, stateW = 320;
  const decH   = 92, decW  = 220;
  const condH  = 60, condW = 240;
  const GAP = 50, TOP = 30, LOOP_OFFSET = 44;
  let y = TOP;
  const layout = els.map(el => {
    const h = el.type === "state" ? stateH : el.type === "decision" ? decH : condH;
    const item = { el, y, h };
    y += h + GAP;
    return item;
  });
  const H = y + 30;
  const parts = [];
  parts.push(`<svg class="asm-svg" xmlns="http://www.w3.org/2000/svg"
                   viewBox="0 0 ${W} ${H}" width="${W}" height="${H}">`);
  parts.push(`<defs>
    <marker id="asm-arrow" viewBox="0 0 10 10" refX="8" refY="5"
            markerWidth="6" markerHeight="6" orient="auto-start-reverse">
      <path d="M0,0 L10,5 L0,10 z" fill="#a8bdd4"/>
    </marker>
    <marker id="asm-arrow-loop" viewBox="0 0 10 10" refX="8" refY="5"
            markerWidth="6" markerHeight="6" orient="auto-start-reverse">
      <path d="M0,0 L10,5 L0,10 z" fill="#fbbf24"/>
    </marker>
  </defs>`);
  const multiText = (x, yTop, text, cls) => {
    const lines = String(text).split(/\n/).filter(Boolean);
    return lines.map((ln, i) =>
      `<text x="${x}" y="${yTop + i*16}" text-anchor="middle" class="${cls}">${esc(ln)}</text>`
    ).join("");
  };
  const findPrevState = (idx) => {
    for (let k = idx - 1; k >= 0; k--)
      if (layout[k].el.type === "state") return layout[k];
    return null;
  };
  const drawNormalDecision = (el, yTop, h, nextTop, isLast) => {
    const decMidY = yTop + h/2;
    if (!isLast){
      const mergeY = nextTop - 22;
      parts.push(`<path class="flow-line" d="M ${CX - decW/2} ${decMidY} L ${CX - decW/2 - 30} ${decMidY} L ${CX - decW/2 - 30} ${mergeY} L ${CX} ${mergeY}"/>`);
      parts.push(`<path class="flow-line" d="M ${CX + decW/2} ${decMidY} L ${CX + decW/2 + 30} ${decMidY} L ${CX + decW/2 + 30} ${mergeY} L ${CX} ${mergeY}"/>`);
      parts.push(`<line class="flow-line" x1="${CX}" y1="${mergeY}" x2="${CX}" y2="${nextTop - 4}" marker-end="url(#asm-arrow)"/>`);
    } else {
      const exitY = yTop + h + 40;
      parts.push(`<path class="flow-line" d="M ${CX - decW/2} ${decMidY} L ${CX - decW/2 - 30} ${decMidY} L ${CX - decW/2 - 30} ${exitY}"/>`);
      parts.push(`<path class="flow-line" d="M ${CX + decW/2} ${decMidY} L ${CX + decW/2 + 30} ${decMidY} L ${CX + decW/2 + 30} ${exitY}"/>`);
      parts.push(`<line class="flow-line" x1="${CX - decW/2 - 30}" y1="${exitY}" x2="${CX - decW/2 - 30}" y2="${exitY + 20}" marker-end="url(#asm-arrow)"/>`);
      parts.push(`<line class="flow-line" x1="${CX + decW/2 + 30}" y1="${exitY}" x2="${CX + decW/2 + 30}" y2="${exitY + 20}" marker-end="url(#asm-arrow)"/>`);
    }
  };
  layout.forEach((it, idx) => {
    const { el, y: yTop, h } = it;
    const yBot = yTop + h;
    const isLast = idx === layout.length - 1;
    const next = isLast ? null : layout[idx + 1];
    const nextTop = next ? next.y : null;
    if (el.type === "state"){
      parts.push(`<rect class="box-fill" x="${CX-stateW/2}" y="${yTop}" width="${stateW}" height="${h}" rx="3"/>`);
      parts.push(`<text x="${CX-stateW/2}" y="${yTop-6}" text-anchor="start" class="name-label">${esc(el.name)}</text>`);
      parts.push(`<text x="${CX+stateW/2}" y="${yTop-6}" text-anchor="end" class="code-label">${esc(el.code)}</text>`);
      parts.push(multiText(CX, yTop + 32, el.ops || "", "ops-text"));
    } else if (el.type === "decision"){
      const midY = yTop + h/2;
      parts.push(`<polygon class="dec-fill" points="${CX},${yTop} ${CX+decW/2},${midY} ${CX},${yBot} ${CX-decW/2},${midY}"/>`);
      parts.push(multiText(CX, midY + 4, el.condition || "", "cond-text"));
      parts.push(`<text x="${CX-decW/2 - 6}" y="${midY - 4}" text-anchor="end" class="branch-label">${esc(el.falseLabel || "0")}</text>`);
      parts.push(`<text x="${CX+decW/2 + 6}" y="${midY - 4}" text-anchor="start" class="branch-label">${esc(el.trueLabel || "1")}</text>`);
    } else {
      parts.push(`<rect class="cond-fill" x="${CX-condW/2}" y="${yTop}" width="${condW}" height="${h}" rx="${h/2}"/>`);
      parts.push(multiText(CX, yTop + h/2 + 4, el.outputs || "", "ops-text"));
    }
    if (el.type === "decision" && el.loopFalse && findPrevState(idx)){
      const prevState = findPrevState(idx);
      const decMidY = yTop + h/2;
      const stateMidY = prevState.y + prevState.h / 2;
      const outerWidth = Math.max(stateW, decW);
      const loopX = CX - outerWidth/2 - LOOP_OFFSET;
      parts.push(`<path class="flow-line loop-line"
        d="M ${CX - decW/2} ${decMidY} L ${loopX} ${decMidY} L ${loopX} ${stateMidY} L ${CX - stateW/2 - 4} ${stateMidY}"
        marker-end="url(#asm-arrow-loop)"/>`);
      parts.push(`<text x="${loopX + 4}" y="${(decMidY + stateMidY)/2 + 4}" class="loop-tag">↻</text>`);
      if (!isLast){
        const mergeY = nextTop - 22;
        parts.push(`<path class="flow-line" d="M ${CX + decW/2} ${decMidY} L ${CX + decW/2 + 30} ${decMidY} L ${CX + decW/2 + 30} ${mergeY} L ${CX} ${mergeY}"/>`);
        parts.push(`<line class="flow-line" x1="${CX}" y1="${mergeY}" x2="${CX}" y2="${nextTop - 4}" marker-end="url(#asm-arrow)"/>`);
      } else {
        const exitY = yBot + 40;
        parts.push(`<path class="flow-line" d="M ${CX + decW/2} ${decMidY} L ${CX + decW/2 + 30} ${decMidY} L ${CX + decW/2 + 30} ${exitY} L ${CX} ${exitY}"/>`);
        parts.push(`<line class="flow-line" x1="${CX}" y1="${exitY}" x2="${CX}" y2="${exitY + 20}" marker-end="url(#asm-arrow)"/>`);
      }
    } else if (el.type === "decision"){
      drawNormalDecision(el, yTop, h, nextTop, isLast);
    } else {
      if (!isLast){
        parts.push(`<line class="flow-line" x1="${CX}" y1="${yBot + 4}" x2="${CX}" y2="${nextTop - 4}" marker-end="url(#asm-arrow)"/>`);
      } else {
        parts.push(`<line class="flow-line" x1="${CX}" y1="${yBot + 4}" x2="${CX}" y2="${yBot + 26}" marker-end="url(#asm-arrow)"/>`);
      }
    }
  });
  parts.push(`</svg>`);
  cv.innerHTML = parts.join("");
}

function renderASM(){
  renderASMList();
  renderASMChart();
}

function initASM(){
  $$(".add-btn").forEach(b => b.addEventListener("click", () => asmAdd(b.dataset.add)));
  $("#asmClear").addEventListener("click", () => {
    if (!asmState.elements.length) return;
    if (!confirm("Clear the entire ASM chart?")) return;
    asmState.elements = [];
    renderASM();
  });
  $("#asmLoadDemo").addEventListener("click", () => {
    asmState.elements = [
      { type: "state", name: "S0", code: "00", ops: "M = 0" },
      { type: "decision", condition: "X = 1?", trueLabel: "1", falseLabel: "0", loopFalse: true },
      { type: "state", name: "S1", code: "01", ops: "M = 1" },
      { type: "conditional", outputs: "Y = 1" },
      { type: "decision", condition: "Z = 1?", trueLabel: "1", falseLabel: "0", loopFalse: true },
      { type: "state", name: "S2", code: "10", ops: "M = 0" }
    ];
    renderASM();
  });
  initAutoGen();
  renderASM();
}

/* ==================================================================
   3b · AUTO GENERATE MODAL
   ================================================================== */
const autoGenState = { configs: [] };

function initAutoGen(){
  const overlay = $("#autoGenModal");
  const statesInput = $("#autoGenStates");
  const configBox = $("#autoGenConfig");
  const open = () => {
    overlay.classList.add("open");
    overlay.setAttribute("aria-hidden", "false");
    rebuildConfigRows(parseInt(statesInput.value, 10) || 3);
    setTimeout(() => statesInput.focus(), 40);
  };
  const close = () => {
    overlay.classList.remove("open");
    overlay.setAttribute("aria-hidden", "true");
  };
  function rebuildConfigRows(n){
    n = Math.max(1, Math.min(8, n | 0));
    autoGenState.configs = [];
    for (let i = 0; i < n; i++){
      autoGenState.configs.push({ condition: `X${i} = 1?`, loopFalse: true });
    }
    renderConfigRows();
  }
  function renderConfigRows(){
    configBox.innerHTML = "";
    autoGenState.configs.forEach((cfg, i) => {
      const row = document.createElement("div");
      row.className = "ag-row";
      row.innerHTML = `
        <span class="ag-state">S${i}</span>
        <input class="ag-cond" value="${esc(cfg.condition)}" spellcheck="false"
               placeholder="e.g. X${i} = 1?">
        <label class="ag-toggle">
          <input type="checkbox" ${cfg.loopFalse ? "checked" : ""}>
          <span>self-loop on 0</span>
        </label>`;
      row.querySelector(".ag-cond").addEventListener("input", e => { cfg.condition = e.target.value; });
      row.querySelector("input[type=checkbox]").addEventListener("change", e => { cfg.loopFalse = e.target.checked; });
      configBox.appendChild(row);
    });
  }
  statesInput.addEventListener("input", () => {
    const n = parseInt(statesInput.value, 10) || 1;
    const old = autoGenState.configs;
    autoGenState.configs = [];
    for (let i = 0; i < Math.max(1, Math.min(8, n)); i++){
      autoGenState.configs.push(old[i] || { condition: `X${i} = 1?`, loopFalse: true });
    }
    renderConfigRows();
  });
  $("#asmAutoGen").addEventListener("click", open);
  $("#autoGenClose").addEventListener("click", close);
  $("#autoGenCancel").addEventListener("click", close);
  overlay.addEventListener("click", e => { if (e.target === overlay) close(); });
  document.addEventListener("keydown", e => {
    if (e.key === "Escape" && overlay.classList.contains("open")) close();
  });
  $("#autoGenConfirm").addEventListener("click", () => {
    generateChartFromConfig();
    close();
  });
}

function generateChartFromConfig(){
  const n = Math.max(1, Math.min(8, parseInt($("#autoGenStates").value, 10) || 1));
  const configs = autoGenState.configs.slice(0, n);
  const elements = [];
  for (let i = 0; i < n; i++){
    elements.push({
      type: "state", name: "S" + i,
      code: i.toString(2).padStart(Math.max(2, Math.ceil(Math.log2(n + 1))), "0"),
      ops: `M = ${i % 2}`
    });
    const cfg = configs[i] || { condition: `X${i} = 1?`, loopFalse: true };
    elements.push({
      type: "decision",
      condition: cfg.condition,
      trueLabel: "1", falseLabel: "0",
      loopFalse: !!cfg.loopFalse
    });
  }
  asmState.elements = elements;
  renderASM();
  const cv = $("#asmCanvas");
  if (cv) cv.scrollIntoView({ behavior: "smooth", block: "nearest" });
}

/* ==================================================================
   4 · EXAMPLES GRID
   ================================================================== */
const EXAMPLES = [
  { tag:"PLD · 2 vars", name:"Half Adder", desc:"Sum and Carry for two 1-bit inputs.",
    eq:"S = A ⊕ B\nCout = A · B", preset:"halfadder" },
  { tag:"PLD · 3 vars", name:"Full Adder", desc:"One-bit adder with carry-in and carry-out.",
    eq:"S = Σm(1,2,4,7)\nCout = Σm(3,5,6,7)", preset:"fulladder" },
  { tag:"PLD · 3 vars", name:"Two Functions · Shared Terms",
    desc:"Classic two-function PLA minimization with a shared product term.",
    eq:"F1 = Σm(1,4,5)\nF2 = Σm(1,3,5)", preset:"ex-3var" },
  { tag:"PLD · 4 vars", name:"Three Functions · Multi-Output PLA",
    desc:"Four-variable design with three outputs sharing six product terms.",
    eq:"F1 = Σm(1,2,3,6,9,11)\nF2 = Σm(0,1,2,6,8,9)\nF3 = Σm(2,3,8,9,11)", preset:"ex-4var" },
  { tag:"PLD · 3 vars", name:"Overlapping Functions",
    desc:"Two overlapping functions that share minterms 2 and 5.",
    eq:"F1 = Σm(0,2,5,7)\nF2 = Σm(2,3,4,5)", preset:"ex-alt" },
  { tag:"PLD · 3 vars", name:"Gray → Binary (partial)",
    desc:"Middle and low binary bits from a 3-bit Gray code.",
    eq:"B2 = Σm(1,2,5,6)\nB1 = Σm(1,3,4,6)\nB0 = Σm(1,4)", preset:"gray2bin" }
];

function renderExamples(){
  const grid = $("#examplesGrid");
  grid.innerHTML = "";
  EXAMPLES.forEach(ex => {
    const card = document.createElement("div");
    card.className = "ex-card";
    card.innerHTML = `
      <span class="ex-tag">${esc(ex.tag)}</span>
      <h3>${esc(ex.name)}</h3>
      <p>${esc(ex.desc)}</p>
      <div class="ex-eq">${esc(ex.eq).replace(/\n/g,"<br>")}</div>`;
    card.addEventListener("click", () => applyPreset(ex.preset));
    grid.appendChild(card);
  });
}

/* ==================================================================
   5 · BOOT
   ================================================================== */
function init(){
  initNav();
  initASM();
  initPLD();
  renderExamples();
  synthesizePLD();
  console.log("ASM & PLD Studio — pla-pal-prom-v7 loaded");
}

document.addEventListener("DOMContentLoaded", init);