'use strict';

/**
 * CAPUNGA DADOS — BAC BO · v20
 *
 * O que mudou em relação à v19 (baseado em 3.044 sinais reais do canal):
 *  - NUNCA força sinal. Os 91 sinais "OPORTUNIDADE FORÇADA" tiveram 33% de loss (normais: 8,5%).
 *  - Não gera sinal com API parada (última rodada > freshMaxMs). Ao voltar: aquece N rodadas
 *    contíguas e pula o 1º sinal.
 *  - Janela de leitura do live igual à do backtest (quebra no buraco de rodadas).
 *  - Confiança deixa de ser nota fixa 80–95: agora é taxa histórica estimada (até G1 / até G2),
 *    com encolhimento bayesiano para a média geral. Ranking e filtros usam essa taxa.
 *  - Estratégias com resultado ruim comprovado ficam bloqueadas (CFG.blockKeys).
 *  - Proteção de banca: pausa após 2 LOSS seguidos e stop de loss do dia.
 *  - Placar honesto: mostra % sem gale e % de loss.
 *  - Correções: hora do sinal (aparecia 01:00:00), IDs de sinal repetidos após reset do estado,
 *    estatísticas que congelavam quando o histórico chegava a 4000 rodadas.
 *
 * Importante: Bac Bo é aleatório. Nada aqui prevê a próxima rodada; são filtros de qualidade de
 * dados e de risco. Meça sempre pelo placar real (sem gale / até G1 / até G2 / loss).
 *
 * Env: BOT_TOKEN, CHAT_ID, ADMIN_TOKEN, DATABASE_URL, PORT,
 *      API_BACBO (opcional), API_BACBO_2 (opcional), ALERT_CHAT_ID (opcional: alertas só para você)
 */

const fs = require('fs');
const crypto = require('crypto');
const express = require('express');
const cors = require('cors');
const axios = require('axios');
const { Pool } = require('pg');

const PORT = Number(process.env.PORT || 10000);
const BOT_TOKEN = process.env.BOT_TOKEN || '';
const CHAT_ID = process.env.CHAT_ID || '';
const ALERT_CHAT_ID = process.env.ALERT_CHAT_ID || CHAT_ID;
const ADMIN_TOKEN = process.env.ADMIN_TOKEN || '';
const DATABASE_URL = process.env.DATABASE_URL || '';

const CFG = {
  ativos: true,
  maxGale: 2,
  maxPending: 1,
  minAmostra: 60,
  syncMs: 3000,                 // polling normal
  syncFastMs: 1000,             // polling com sinal pendente / mesa quente
  minGapMs: 20000,              // entre sinais
  relaxMs: 3 * 60 * 1000,       // 3min sem sinal -> critério relaxado (tier 1). NÃO existe mais tier forçado.
  minSettledAgeMs: 5000,
  freshMaxMs: 2 * 60 * 1000,    // última rodada precisa ter menos de 2 min
  windowGapMs: 4 * 60 * 1000,   // buraco entre rodadas que quebra a janela de leitura
  warmupRounds: 6,              // rodadas contíguas mínimas antes de sinalizar
  postGapSkip: 1,               // pula N sinais depois que a API volta
  apuraMaxMs: 600000,
  maxHist: 4000,
  gapMs: 7 * 60 * 1000,         // buraco que expira a entrada pendente
  maxSignalsMem: 500,
  signalsOnBoot: 500,
  suspendMs: 4 * 3600 * 1000,
  suspendLossStreak: 3,         // 3 LOSS seguidos da mesma estratégia -> suspende
  suspendWindow: 12,            // ou: nos últimos 12 sinais da estratégia...
  suspendWindowLosses: 4,       // ...4 ou mais LOSS -> suspende
  staleAlertMs: 3 * 60 * 1000,
  alertThrottleMs: 10 * 60 * 1000,
  keepAliveMs: 60000,
  priorK: 10,                   // peso da média geral no encolhimento bayesiano
  blockKeys: ['SEQ_3_1'],       // "3→1 confirmado": 26% de loss na amostra real
  // candidatas a bloqueio (amostra pequena, avalie): 'SEQ_REP_5', 'NUM_REPETE', 'TIE_SINGLE'
  lossPauseAfter: 2,            // 2 LOSS seguidos -> pausa geral
  lossPauseMs: 15 * 60 * 1000,
  maxLossDia: 6,                // stop de loss do dia (zera às 00h00 de Angola)
  // Tiers: 0 = rigoroso, 1 = relaxado (após relaxMs sem sinal). dP1 é relativo à média geral até G1.
  tiers: [
    { minN: 10, dP1: -0.01, liveMin: 0.86 },
    { minN: 5, dP1: -0.04, liveMin: 0.80 }
  ]
};

const J = 'Jogador';
const B = 'Banca';
const E = 'Empate';
const isCol = (x) => x === J || x === B;
const opp = (c) => (c === J ? B : c === B ? J : null);
const FECHADOS = new Set(['GREEN', 'G1', 'G2', 'EMPATE', 'EG1', 'EG2', 'LOSS']);
const ATE_G1 = new Set(['GREEN', 'EMPATE', 'G1', 'EG1']);
const LOCK_KEY = 727272;

const API_SOURCES = [
  process.env.API_BACBO ||
    'https://api-cs.casino.org/svc-evolution-game-events/api/bacbo?page=0&size=50&sort=data.settledAt,desc&duration=120&wheelResults=PlayerWon,BankerWon,Tie',
  process.env.API_BACBO_2 || ''
].filter(Boolean);

const DEPLOY_ID = (() => {
  if (process.env.DEPLOY_ID) return String(process.env.DEPLOY_ID).trim();
  try { return crypto.createHash('sha256').update(fs.readFileSync(__filename)).digest('hex').slice(0, 16); }
  catch { return 'unknown'; }
})();

const S = {
  hist: [], seen: new Set(), signals: [],
  nextId: 1, lastSignalAt: 0, curStreak: 0,
  stats: null, novosDesdeStats: 0,
  apiWasDown: false, skipNext: 0, skipRoundId: null,
  lossRun: 0, pauseUntil: 0
};

// Placar DIÁRIO (zera 00h00 Angola = UTC+1)
const DAILY = { date: '', total: 0, green: 0, g1: 0, g2: 0, empate: 0, eg1: 0, eg2: 0, loss: 0, bestStreak: 0 };
// Placar GERAL (persistente)
const ALLTIME = { total: 0, green: 0, g1: 0, g2: 0, empate: 0, eg1: 0, eg2: 0, loss: 0 };
const SUSPENDED = {};

const R = {
  iniciadoEm: new Date().toISOString(), deployId: DEPLOY_ID, versao: '20.0',
  ultimaSync: null, ultimaRodadaNova: null, fonteAPI: 0,
  erroAPI: null, erroTelegram: null, erroDB: null,
  ultimoMotivo: null, ultimoSinal: null, tier: 0, wakes: 0, ultimoWake: null,
  ultimoAlertaAPI: 0, ultimoAlertaDB: 0, lockOk: false
};

let pool = null, server = null, tickTimer = null, keepTimer = null;
let busy = false, stopping = false, lastTickMs = Date.now();

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const log = (tag, d) => console.log(`[${new Date().toISOString()}] [${tag}] ${typeof d === 'string' ? d : JSON.stringify(d)}`);
const clamp = (x, a, b) => Math.max(a, Math.min(b, x));

const fmtHora = new Intl.DateTimeFormat('pt-PT', {
  timeZone: 'Africa/Luanda', hour: '2-digit', minute: '2-digit', second: '2-digit', hour12: false
});
const hora = (ms = Date.now()) => fmtHora.format(new Date(ms));
// Meia-noite em Angola (UTC+1, sem horário de verão)
const luandaDayKey = (ms = Date.now()) => new Date(ms + 3600000).toISOString().slice(0, 10);

const nomeCor = (c) => (c === B ? 'VERMELHO 🔴' : c === J ? 'AZUL 🔵' : 'EMPATE 🟡');

/* ============================ DB ============================ */

async function dbInit() {
  if (!DATABASE_URL) { log('DB', 'sem persistência'); return; }
  try {
    const local = /^postgres(?:ql)?:\/\/[^@]*@?(localhost|127\.0\.0\.1)(:|\/|$)/i.test(DATABASE_URL);
    pool = new Pool({
      connectionString: DATABASE_URL,
      ssl: local ? false : { rejectUnauthorized: false },
      max: 6
    });
    await pool.query('SELECT 1');
    await pool.query(`
      CREATE TABLE IF NOT EXISTS capunga_state (k TEXT PRIMARY KEY, v TEXT NOT NULL, updated_at TIMESTAMPTZ DEFAULT NOW());
      CREATE TABLE IF NOT EXISTS capunga_rounds (id TEXT PRIMARY KEY, resultado TEXT NOT NULL, t BIGINT NOT NULL, pj DOUBLE PRECISION, pb DOUBLE PRECISION);
      CREATE INDEX IF NOT EXISTS idx_cap_rounds_t ON capunga_rounds(t DESC);
      CREATE TABLE IF NOT EXISTS capunga_signals (
        id INTEGER PRIMARY KEY, cor TEXT NOT NULL, key TEXT NOT NULL, nome TEXT NOT NULL,
        tipo TEXT NOT NULL, conf INT NOT NULL, status TEXT NOT NULL DEFAULT 'PENDENTE',
        gale INT, agree INT, tier INT DEFAULT 0, created_at TIMESTAMPTZ NOT NULL, closed_at TIMESTAMPTZ
      );
      CREATE INDEX IF NOT EXISTS idx_cap_sig_status ON capunga_signals(status);
      CREATE INDEX IF NOT EXISTS idx_cap_sig_created ON capunga_signals(created_at DESC);
    `);
    R.erroDB = null; log('DB', 'schema ok');
  } catch (e) { R.erroDB = e.message; log('DB ERRO', e.message); pool = null; }
}

async function acquireLock() {
  if (!pool) return false;
  for (let i = 1; i <= 10; i++) {
    try {
      const r = await pool.query('SELECT pg_try_advisory_lock($1) AS ok', [LOCK_KEY]);
      if (r.rows[0].ok) { R.lockOk = true; return true; }
      log('LOCK', `instância concorrente detectada — tentativa ${i}/10`);
    } catch (e) { R.erroDB = e.message; log('LOCK ERRO', e.message); }
    await sleep(15000);
  }
  return false;
}
async function releaseLock() {
  if (!pool || !R.lockOk) return;
  try { await pool.query('SELECT pg_advisory_unlock($1)', [LOCK_KEY]); } catch (_) {}
}

async function dbStateGet(k) {
  if (!pool) return null;
  try { const r = await pool.query('SELECT v FROM capunga_state WHERE k=$1', [k]); return r.rows[0]?.v ?? null; }
  catch (e) { R.erroDB = e.message; return null; }
}
async function dbStateSet(k, v) {
  if (!pool) return;
  try {
    await pool.query(
      `INSERT INTO capunga_state(k,v,updated_at) VALUES ($1,$2,NOW())
       ON CONFLICT (k) DO UPDATE SET v=EXCLUDED.v, updated_at=NOW()`, [k, String(v)]);
  } catch (e) { R.erroDB = e.message; }
}
async function dbSignalInsert(s) {
  if (!pool) return;
  try {
    await pool.query(
      `INSERT INTO capunga_signals (id,cor,key,nome,tipo,conf,status,gale,agree,tier,created_at,closed_at)
       VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10,$11,$12) ON CONFLICT (id) DO NOTHING`,
      [s.id, s.cor, s.key, s.nome, s.tipo, s.conf, s.status, s.gale ?? null, s.agree ?? 1, s.tier ?? 0,
        new Date(s.t), s.fechadoEm ? new Date(s.fechadoEm) : null]);
  } catch (e) { R.erroDB = e.message; }
}
async function dbSignalUpdate(s) {
  if (!pool) return;
  try {
    await pool.query('UPDATE capunga_signals SET status=$1, gale=$2, closed_at=$3 WHERE id=$4',
      [s.status, s.gale ?? null, s.fechadoEm ? new Date(s.fechadoEm) : null, s.id]);
  } catch (e) { R.erroDB = e.message; }
}
async function dbRoundUpsert(r) {
  if (!pool) return;
  try {
    await pool.query(
      `INSERT INTO capunga_rounds(id,resultado,t,pj,pb) VALUES($1,$2,$3,$4,$5)
       ON CONFLICT(id) DO UPDATE SET resultado=EXCLUDED.resultado,t=EXCLUDED.t,pj=EXCLUDED.pj,pb=EXCLUDED.pb`,
      [r.id, r.resultado, r.t, r.pj, r.pb]);
  } catch (e) { R.erroDB = e.message; }
}

async function dbLoadAlltime() {
  if (!pool) return;
  try {
    const r = await pool.query(
      `SELECT status, COUNT(*)::int AS n FROM capunga_signals
       WHERE status <> 'PENDENTE' GROUP BY status`);
    for (const k of Object.keys(ALLTIME)) ALLTIME[k] = 0;
    for (const row of r.rows) {
      ALLTIME.total += row.n;
      if (row.status === 'GREEN') ALLTIME.green = row.n;
      else if (row.status === 'G1') ALLTIME.g1 = row.n;
      else if (row.status === 'G2') ALLTIME.g2 = row.n;
      else if (row.status === 'EMPATE') ALLTIME.empate = row.n;
      else if (row.status === 'EG1') ALLTIME.eg1 = row.n;
      else if (row.status === 'EG2') ALLTIME.eg2 = row.n;
      else if (row.status === 'LOSS') ALLTIME.loss = row.n;
    }
  } catch (e) { R.erroDB = e.message; }
}

async function dbLoadState() {
  if (!pool) return;
  try {
    const nextId = await dbStateGet('nextId');
    const lastSignalAt = await dbStateGet('lastSignalAt');
    const curStreak = await dbStateGet('curStreak');
    const pauseUntil = await dbStateGet('pauseUntil');
    if (nextId) S.nextId = Math.max(1, parseInt(nextId, 10));
    if (lastSignalAt) S.lastSignalAt = parseInt(lastSignalAt, 10);
    if (curStreak) S.curStreak = parseInt(curStreak, 10);
    if (pauseUntil) S.pauseUntil = parseInt(pauseUntil, 10) || 0;

    // FIX v20: se o estado 'nextId' foi perdido/zerado, nunca reutilizar IDs que já existem na tabela
    // (antes: INSERT ... ON CONFLICT DO NOTHING + UPDATE por id corrompia sinais antigos).
    try {
      const mx = await pool.query('SELECT COALESCE(MAX(id),0)::int AS m FROM capunga_signals');
      const m = mx.rows[0]?.m || 0;
      if (S.nextId <= m) { S.nextId = m + 1; await dbStateSet('nextId', String(S.nextId)); }
    } catch (_) {}

    try {
      const raw = await dbStateGet('suspended');
      if (raw) {
        const arr = JSON.parse(raw);
        const now = Date.now();
        for (const [key, until] of arr) if (until > now) SUSPENDED[key] = until;
      }
    } catch (_) {}

    // Placar diário persistido
    try {
      const rawD = await dbStateGet('daily_v19');
      if (rawD) Object.assign(DAILY, JSON.parse(rawD));
    } catch (_) {}
    if (!DAILY.date) DAILY.date = luandaDayKey();

    const rounds = await pool.query(`SELECT id,resultado,t,pj,pb FROM capunga_rounds ORDER BY t DESC LIMIT ${CFG.maxHist}`);
    S.hist = rounds.rows.map((r) => ({
      id: r.id, resultado: r.resultado, t: Number(r.t),
      pj: r.pj === null ? null : Number(r.pj), pb: r.pb === null ? null : Number(r.pb)
    })).reverse();
    S.seen = new Set(S.hist.map((r) => r.id));
    const r = await pool.query(`SELECT * FROM capunga_signals ORDER BY created_at DESC LIMIT ${CFG.signalsOnBoot}`);
    S.signals = r.rows.reverse().map((row) => ({
      id: row.id, cor: row.cor, key: row.key, nome: row.nome, tipo: row.tipo,
      conf: row.conf, status: row.status, gale: row.gale, agree: row.agree, tier: row.tier || 0,
      t: new Date(row.created_at).getTime(), criadoEm: new Date(row.created_at).getTime(),
      fechadoEm: row.closed_at ? new Date(row.closed_at).getTime() : null,
      gale1MsgId: null, gale2MsgId: null, galeLevel: row.status !== 'PENDENTE' ? 2 : 0
    }));
    await dbLoadAlltime();
    log('DB', `estado carregado: nextId=${S.nextId}, sinais=${S.signals.length}, diário=${DAILY.date}`);
  } catch (e) { R.erroDB = e.message; log('DB ERRO load', e.message); }
}

/* ============================ TELEGRAM ============================ */

async function tgSendRaw(texto, chatId = CHAT_ID) {
  if (!BOT_TOKEN || !chatId) { R.erroTelegram = 'TOKEN/CHAT em falta'; return { ok: false }; }
  for (let t = 1; t <= 3; t++) {
    try {
      const r = await axios.post(`https://api.telegram.org/bot${BOT_TOKEN}/sendMessage`,
        { chat_id: chatId, text: texto, parse_mode: 'HTML', disable_web_page_preview: true },
        { timeout: 11000 });
      if (r.data?.ok) { R.erroTelegram = null; return { ok: true, messageId: r.data.result.message_id }; }
      R.erroTelegram = JSON.stringify(r.data);
    } catch (e) {
      R.erroTelegram = e.response?.data ? JSON.stringify(e.response.data) : e.message;
      const retry = Number(e.response?.data?.parameters?.retry_after);
      if (retry > 0 && retry <= 20) await sleep(retry * 1000 + 200);
    }
    if (t < 3) await sleep(1100 * t);
  }
  return { ok: false };
}
async function tgDelete(messageId) {
  if (!messageId || !BOT_TOKEN || !CHAT_ID) return;
  try {
    await axios.post(`https://api.telegram.org/bot${BOT_TOKEN}/deleteMessage`,
      { chat_id: CHAT_ID, message_id: messageId }, { timeout: 8000 });
  } catch (_) {}
}
// Alertas técnicos vão para ALERT_CHAT_ID (se definido) para não aparecerem no canal dos membros
async function tgAlert(tag, detalhe) {
  const now = Date.now();
  if (tag === 'API') {
    if (now - R.ultimoAlertaAPI < CFG.alertThrottleMs) return;
    R.ultimoAlertaAPI = now;
  }
  if (tag === 'DB') {
    if (now - R.ultimoAlertaDB < CFG.alertThrottleMs) return;
    R.ultimoAlertaDB = now;
  }
  await tgSendRaw(`⚠️ <b>ALERTA ${tag}</b>\n${detalhe}\n⏱ ${hora()}`, ALERT_CHAT_ID);
}

/* ============================ PLACAR ============================ */

function dailyWins() { return DAILY.green + DAILY.g1 + DAILY.g2 + DAILY.empate + DAILY.eg1 + DAILY.eg2; }
function dailyTaxa() { return DAILY.total > 0 ? (dailyWins() / DAILY.total) * 100 : 0; }
function dailySemGale() { return DAILY.total > 0 ? ((DAILY.green + DAILY.empate) / DAILY.total) * 100 : 0; }
function dailyLossPct() { return DAILY.total > 0 ? (DAILY.loss / DAILY.total) * 100 : 0; }

async function sendDailySummary(ontem) {
  const wins = dailyWins();
  await tgSendRaw([
    `🕛 <b>FIM DO DIA ${ontem}</b> 🕛`,
    '',
    `📊 Sinais: <b>${DAILY.total}</b>`,
    `✅ Greens: ${wins} (G1: ${DAILY.g1} • G2: ${DAILY.g2})`,
    `🟡 Empates: ${DAILY.empate + DAILY.eg1 + DAILY.eg2}`,
    `❌ Loss: ${DAILY.loss}`,
    `🔥 Maior sequência: ${DAILY.bestStreak}`,
    `🎯 Taxa (até G2): ${dailyTaxa().toFixed(1)}%`,
    `⚠️ Sem gale: ${dailySemGale().toFixed(0)}% • Loss: ${dailyLossPct().toFixed(1)}%`,
    '',
    '🌅 <b>PLACAR ZERADO — BOM DIA!</b>'
  ].join('\n'));
}

async function checkDailyReset() {
  const hoje = luandaDayKey();
  if (DAILY.date && DAILY.date !== hoje) {
    const ontem = DAILY.date;
    await sendDailySummary(ontem);
    for (const k of ['total', 'green', 'g1', 'g2', 'empate', 'eg1', 'eg2', 'loss', 'bestStreak']) DAILY[k] = 0;
    DAILY.date = hoje;
    S.lossRun = 0;
    await dbStateSet('daily_v19', JSON.stringify(DAILY));
    log('DIÁRIO', `reset de ${ontem} -> ${hoje}`);
  } else if (!DAILY.date) {
    DAILY.date = hoje;
  }
}

/* ============================ ESTATÍSTICA POR ESTRATÉGIA ============================ */

// Histórico "real" de uma estratégia: backtest + sinais fechados recentes (janela de S.signals)
function histReal(key) {
  let n = 0, g01 = 0, w = 0;
  for (const x of S.signals) {
    if (x.key !== key || !FECHADOS.has(x.status)) continue;
    n++;
    if (x.status !== 'LOSS') w++;
    if (ATE_G1.has(x.status)) g01++;
  }
  return { n, g01, w };
}

/* ============================ TEMPLATES ============================ */

function fmtAnalisando() {
  return [`⚙️ <b>CAPUNGA v20 — Lendo a mesa…</b>`, `⏱ ${hora()}`].join('\n');
}

function fmtSinal(s) {
  const tierTag = s.tier >= 1 ? '\n🔎 <i>Mesa mais lenta — critério relaxado, gestão redobrada</i>' : '';
  const h = histReal(s.key);
  const histTxt = h.n >= 10
    ? `📊 Histórico real: ${Math.round((h.g01 / h.n) * 100)}% até G1 · ${Math.round((h.w / h.n) * 100)}% até G2 (n=${h.n})`
    : `📊 Histórico estimado: ${s.p1 != null ? Math.round(s.p1 * 100) : '--'}% até G1 · ${s.p2 != null ? Math.round(s.p2 * 100) : '--'}% até G2`;
  return [
    `🎲 ═══ <b>CAPUNGA PRIME</b> ═══ 🎲`,
    '',
    `🚨 <b>ENTRADA CONFIRMADA #${s.id}</b>${tierTag}`,
    '',
    `🎯 Entrar: <b>${nomeCor(s.cor)}</b>`,
    `🛡 Proteção: EMPATE 🟡`,
    histTxt,
    `🧠 ${s.emoji || '🧩'} ${s.nome}`,
    `⏰ ${hora(s.t)}`,
    '',
    `💎 <i>Capunga Prime — gestão de banca sempre</i>`
  ].join('\n');
}

function fmtGale(s, nivel) {
  const icons = nivel === 1 ? '🔄' : '⚠️';
  const extra = nivel === 2 ? '\n💰 <i>Dobrar a entrada na mesma cor</i>' : '';
  return [
    `${icons} <b>GALE ${nivel} — SINAL #${s.id}</b> ${icons}`,
    `Mantenha: <b>${nomeCor(s.cor)}</b>${extra}`
  ].join('\n');
}

function fmtResult(s) {
  const placar = `📅 Dia: ${dailyWins()}G • ${DAILY.loss}L • ${dailyTaxa().toFixed(0)}%`;
  const msg = {
    GREEN: `✅ <b>GREEN #${s.id}</b> ✅\n\nA mesa pagou tropa 💚\n${placar}`,
    G1: `✅ <b>GREEN NO GALE 1 #${s.id}</b> ✅\n\nRecuperado com segurança 💪\n${placar}`,
    G2: `✅ <b>GREEN NO GALE 2 #${s.id}</b> ✅\n\nRecuperação total, gestão mandou 🛡\n${placar}`,
    EMPATE: `🟡 <b>GREEN NO EMPATE #${s.id}</b> 🟡\n\nProteção segurou a entrada 🛡\n${placar}`,
    EG1: `🟡 <b>GREEN NO EMPATE G1 #${s.id}</b> 🟡\n\nProteção no gale 🛡\n${placar}`,
    EG2: `🟡 <b>GREEN NO EMPATE G2 #${s.id}</b> 🟡\n\nProteção máxima 🛡\n${placar}`,
    LOSS: `❌ <b>LOSS #${s.id}</b> ❌\n\nStop atingido nesta. Próxima entrada em análise 🧠\n${placar}`
  };
  return msg[s.status] || msg.LOSS;
}

function fmtHistorico() {
  const streak = S.curStreak;
  const streakTxt = streak >= 3 ? `${streak} 🔥` : `${streak}`;
  return [
    `📊 <b>PLACAR DO DIA — ${DAILY.date}</b>`,
    '━━━━━━━━━━━━━━━',
    `Sinais: ${DAILY.total}`,
    `✅ Greens: ${DAILY.green} | G1: ${DAILY.g1} | G2: ${DAILY.g2}`,
    `🟡 Empates: ${DAILY.empate + DAILY.eg1 + DAILY.eg2}`,
    `❌ Loss: ${DAILY.loss}`,
    `🔥 Sequência atual: ${streakTxt} | Recorde: ${DAILY.bestStreak}`,
    `🎯 Taxa do dia (até G2): ${dailyTaxa().toFixed(1)}%`,
    `⚠️ Sem gale: ${dailySemGale().toFixed(0)}% • Loss: ${dailyLossPct().toFixed(1)}%`
  ].join('\n');
}

/* ============================ API ============================ */

// Remove acentos SEM regex de caracteres combinantes (evita corrupção de encoding)
function stripAccents(str) {
  return String(str ?? '').normalize('NFD').split('').filter((c) => {
    const code = c.charCodeAt(0);
    return code < 0x0300 || code > 0x036f;
  }).join('');
}

function normalizeOutcome(v) {
  if (v && typeof v === 'object') v = v.outcome ?? v.resultado ?? v.winner ?? v.name;
  const s = stripAccents(v).trim().toLowerCase().replace(/[\s_-]+/g, '');
  if (['player', 'jogador', 'playerwin', 'playerwins', 'playerwon', 'blue'].includes(s)) return J;
  if (['banker', 'banca', 'bankerwin', 'bankerwins', 'bankerwon', 'red', 'vermelho'].includes(s)) return B;
  if (['tie', 'draw', 'empate', 'equal', 'push', 'tied'].includes(s)) return E;
  return null;
}
const validMs = (v) => { if (!v) return null; const t = new Date(v).getTime(); return Number.isNaN(t) ? null : t; };
function extractItems(b) {
  if (Array.isArray(b)) return b;
  if (!b || typeof b !== 'object') return [];
  return [b.data, b.results, b.items, b.resultados, b.rounds, b.events,
    b.data?.results, b.data?.items, b.data?.resultados, b.data?.rounds,
    b.data?.events, b.data?.data].find(Array.isArray) || [];
}
// null-safe: Number(null) === 0 criaria scores falsos (ex.: Gatilho 0 falso)
const numOrNull = (v) => {
  if (v === null || v === undefined || v === '') return null;
  const n = Number(v);
  return Number.isFinite(n) ? n : null;
};
function normalizeRound(item) {
  const d = item?.data || item?.round || item || {};
  const r = (d.result && typeof d.result === 'object') ? d.result
    : (item?.result && typeof item.result === 'object') ? item.result : {};
  const t = validMs(d.settledAt ?? d.endTime ?? d.endedAt ?? d.finishedAt ?? d.fim ?? item?.settledAt ?? item?.fim);
  const raw = r.outcome ?? r.resultado ?? r.winner ?? d.outcome ?? d.resultado ?? d.winner ??
    item?.outcome ?? item?.resultado ?? item?.winner ??
    (typeof d.result === 'string' ? d.result : null) ??
    (typeof item?.result === 'string' ? item.result : null);
  const resultado = normalizeOutcome(raw);
  const id = String(d.id ?? d.roundId ?? d.round_id ?? d.eventId ?? item?.id ?? item?.roundId ?? item?.round_id ?? item?.eventId ?? '').trim();
  if (!id || !resultado || !t) return null;
  const pj = numOrNull(r.playerDice?.score ?? d.playerDice?.score ?? d.playerScore ?? d.player_score ?? d.pontos_jogador);
  const pb = numOrNull(r.bankerDice?.score ?? d.bankerDice?.score ?? d.bankerScore ?? d.banker_score ?? d.pontos_banca);
  return { id, resultado, t, pj, pb };
}

async function fetchFrom(url) {
  const resp = await axios.get(url, {
    timeout: 10000,
    headers: { Accept: 'application/json', 'User-Agent': 'CapungaDados/20.0' }
  });
  const map = new Map();
  for (const it of extractItems(resp.data)) {
    const rd = normalizeRound(it);
    if (rd) map.set(rd.id, rd);
  }
  return [...map.values()].sort((a, b) => a.t - b.t || (a.id < b.id ? -1 : 1));
}

// Fallback automático entre fontes: se a primária falhar, tenta a secundária
async function fetchRounds() {
  const erros = [];
  for (let idx = 0; idx < API_SOURCES.length; idx++) {
    for (let tentativa = 1; tentativa <= 2; tentativa++) {
      try {
        const rounds = await fetchFrom(API_SOURCES[idx]);
        R.fonteAPI = idx;
        R.erroAPI = null;
        return rounds;
      } catch (e) {
        erros.push(`fonte${idx + 1}: ${e.message}`);
        if (tentativa < 2) await sleep(500);
      }
    }
  }
  R.erroAPI = erros.join(' | ');
  throw new Error(R.erroAPI);
}

/* ============================ HELPERS ============================ */

const hasScore = (r) => r && Number.isFinite(r.pj) && Number.isFinite(r.pb);
const margem = (r) => Math.abs((r.pj || 0) - (r.pb || 0));
const scoreOf = (r) => (r.resultado === J ? r.pj : r.pb);
const scoreRange = (s) => {
  if (!Number.isFinite(s)) return null;
  if (s <= 2) return 'MB';
  if (s <= 4) return 'B';
  if (s <= 6) return 'M';
  if (s <= 8) return 'A';
  return 'MA';
};
function streak(seq) {
  if (!seq.length) return 0;
  let n = 0; const cor = seq[0].resultado;
  for (const r of seq) { if (r.resultado === cor) n++; else break; }
  return n;
}
function alternation(seq) {
  if (seq.length < 2) return 1;
  let L = 1;
  while (L < seq.length && seq[L].resultado !== seq[L - 1].resultado) L++;
  return L;
}
function detectRegime(seq) {
  if (seq.length < 6) return { trend: 0.5, chop: 0.5, label: 'neutro' };
  const n = Math.min(seq.length, 15);
  let changes = 0;
  for (let i = 1; i < n; i++) if (seq[i].resultado !== seq[i - 1].resultado) changes++;
  const chop = changes / (n - 1);
  const trend = 1 - chop;
  const label = chop >= 0.65 ? 'errático' : chop <= 0.35 ? 'tendência' : 'neutro';
  return { trend, chop, label };
}
// Estratégias de quebra só em mesa errática; de sequência só em tendência
function regimeFit(cand, regime) {
  const k = cand.key;
  if (/SEQ_(QUEBRA|SURF|PINGPONG|2x2|EXTEND|3_1|MOMENTUM|ALT|BREAK_WEAK)/.test(k)) return regime.chop >= 0.45;
  if (/SEQ_(REP|STRONG_STREAK)|BANKER_BIAS/.test(k)) return regime.trend >= 0.45;
  return true;
}

/* ============================ ESTRATÉGIAS (30) ============================ */

const STRATS = [
  // ---- SEQUÊNCIA ----
  function seqRepeticao({ seq }) {
    const n = streak(seq);
    if (n < 3 || n > 7) return null;
    const strength = [0, 0, 0, 72, 78, 84, 86, 86][n] || 86;
    return { cor: seq[0].resultado, key: `SEQ_REP_${n}`, nome: `Sequência x${n}`, emoji: '🔁', strength, tipo: 'seq' };
  },
  function seqQuebra({ seq }) {
    const n = streak(seq);
    if (n < 4 || n > 8) return null;
    const strength = [0, 0, 0, 0, 74, 80, 84, 85, 85][n] || 85;
    return { cor: opp(seq[0].resultado), key: `SEQ_QUEBRA_${n}`, nome: `Quebra x${n}`, emoji: '💥', strength, tipo: 'seq' };
  },
  function seqSurf({ seq }) {
    const L = alternation(seq);
    if (L < 4) return null;
    const strength = L >= 6 ? 84 : L >= 5 ? 78 : 72;
    return { cor: opp(seq[0].resultado), key: `SEQ_SURF_${L}`, nome: `Surf ${L}`, emoji: '🌊', strength, tipo: 'seq' };
  },
  function seqDoisDois({ seq }) {
    if (seq.length < 4) return null;
    const [a, b, c, d] = seq.map((x) => x.resultado);
    if (a === b && c === d && a !== c) return { cor: c, key: 'SEQ_2x2', nome: 'Bloco 2+2', emoji: '♟️', strength: 76, tipo: 'seq' };
    return null;
  },
  function seqTresUm({ seq }) {
    if (seq.length < 4) return null;
    const [a, b, c, d] = seq.map((x) => x.resultado);
    if (a !== b && b === c && c === d) return { cor: a, key: 'SEQ_3_1', nome: '3→1 confirmado', emoji: '🧩', strength: 78, tipo: 'seq' };
    return null;
  },
  function seqMomentum2({ seq }) {
    if (seq.length < 3) return null;
    const [a, b, c] = seq.map((x) => x.resultado);
    if (a !== b && b === c) return { cor: c, key: 'SEQ_MOMENTUM_2', nome: 'Momentum 2', emoji: '⚡', strength: 77, tipo: 'seq' };
    return null;
  },
  function seqBreakWeak4({ seq }) {
    const n = streak(seq);
    if (n !== 4) return null;
    const s = seq.slice(0, 4);
    if (!s.every((r) => hasScore(r) && margem(r) <= 2)) return null;
    return { cor: opp(seq[0].resultado), key: 'SEQ_BREAK_WEAK_4', nome: 'Quebra fraca x4', emoji: '🩹', strength: 79, tipo: 'seq' };
  },
  function seqExtend({ seq }) {
    if (seq.length < 5) return null;
    const [a, b, c, d, e] = seq.map((x) => x.resultado);
    if (a === b && b === c && c !== d && d === e) {
      return { cor: a, key: 'SEQ_EXTEND', nome: 'Streak extend', emoji: '⏭️', strength: 80, tipo: 'seq' };
    }
    return null;
  },
  function seqStrongStreak({ seq }) {
    const n = streak(seq);
    if (n < 4 || n > 6) return null;
    const same = seq.slice(0, n);
    if (!same.every((r) => hasScore(r) && margem(r) >= 3)) return null;
    return { cor: seq[0].resultado, key: 'SEQ_STRONG_STREAK', nome: `Dragon ${n}`, emoji: '🐉', strength: 82, tipo: 'seq' };
  },
  function seqPingPong({ seq }) {
    const L = alternation(seq);
    if (L < 4 || L > 10) return null;
    return { cor: opp(seq[0].resultado), key: 'SEQ_PINGPONG', nome: `Ping-pong ${L}`, emoji: '🏓', strength: 79, tipo: 'seq' };
  },
  function seqAlternatingStrong({ seq }) {
    const L = alternation(seq);
    if (L < 3) return null;
    const s = seq.slice(0, L);
    if (!s.every((r) => hasScore(r) && margem(r) >= 3)) return null;
    return { cor: opp(seq[0].resultado), key: 'SEQ_ALT_STRONG', nome: `Alt. forte ${L}`, emoji: '⚔️', strength: 78, tipo: 'seq' };
  },
  function bankerBias20({ seq }) {
    const s = seq.slice(0, 20);
    if (s.length < 15) return null;
    const b = s.filter((r) => r.resultado === B).length;
    const j = s.filter((r) => r.resultado === J).length;
    if (b >= 12) return { cor: B, key: 'BANKER_BIAS_20', nome: 'Viés Banca', emoji: '📉', strength: 80, tipo: 'seq' };
    if (j >= 12) return { cor: J, key: 'BANKER_BIAS_20', nome: 'Viés Jogador', emoji: '📈', strength: 80, tipo: 'seq' };
    return null;
  },
  // ---- NUMÉRICA ----
  function numEscada({ seq }) {
    if (seq.length < 3 || !seq.slice(0, 3).every(hasScore)) return null;
    const [a, b, c] = seq;
    if (a.resultado !== b.resultado || b.resultado !== c.resultado) return null;
    const sa = scoreOf(a), sb = scoreOf(b), sc = scoreOf(c);
    if ((sb - sa === 1 && sc - sb === 1) || (sa - sb === 1 && sb - sc === 1)) {
      return { cor: a.resultado, key: 'NUM_ESCADA', nome: `Escada ${sa}→${sb}→${sc}`, emoji: '🪜', strength: 88, tipo: 'num' };
    }
    return null;
  },
  function numRepeteScore({ seq }) {
    if (seq.length < 2 || !hasScore(seq[0]) || !hasScore(seq[1])) return null;
    const [a, b] = seq;
    if (a.resultado !== b.resultado) return null;
    if (scoreOf(a) === scoreOf(b)) return { cor: a.resultado, key: 'NUM_REPETE', nome: `Score repetido ${scoreOf(a)}`, emoji: '🔂', strength: 84, tipo: 'num' };
    return null;
  },
  function numThreeLow({ seq }) {
    if (seq.length < 3 || !seq.slice(0, 3).every(hasScore)) return null;
    const [a, b, c] = seq;
    if (a.resultado !== b.resultado || b.resultado !== c.resultado) return null;
    if (scoreOf(a) <= 3 && scoreOf(b) <= 3 && scoreOf(c) <= 3) {
      return { cor: opp(a.resultado), key: 'NUM_THREE_LOW', nome: 'Virada de baixos x3', emoji: '📉', strength: 81, tipo: 'num' };
    }
    return null;
  },
  function numGatilho_0({ seq }) {
    if (!seq.length || !hasScore(seq[0])) return null;
    if (scoreOf(seq[0]) === 0) return { cor: opp(seq[0].resultado), key: 'NUM_GATILHO_0', nome: 'Gatilho 0', emoji: '🎯', strength: 86, tipo: 'num' };
    return null;
  },
  function numGatilho_1({ seq }) {
    if (!seq.length || !hasScore(seq[0])) return null;
    if (scoreOf(seq[0]) === 1) return { cor: opp(seq[0].resultado), key: 'NUM_GATILHO_1', nome: 'Gatilho 1', emoji: '🎯', strength: 84, tipo: 'num' };
    return null;
  },
  function numGatilho_9({ seq }) {
    if (!seq.length || !hasScore(seq[0])) return null;
    if (scoreOf(seq[0]) === 9) return { cor: opp(seq[0].resultado), key: 'NUM_GATILHO_9', nome: 'Gatilho 9', emoji: '🎯', strength: 88, tipo: 'num' };
    return null;
  },
  function numMargemAlta({ rows }) {
    const r = rows[0];
    if (!r || !isCol(r.resultado) || !hasScore(r) || margem(r) < 5) return null;
    return { cor: r.resultado, key: 'NUM_MARGEM5', nome: `Margem alta ${r.pj}×${r.pb}`, emoji: '📊', strength: 82, tipo: 'num' };
  },
  function numDiff4x3({ seq }) {
    if (seq.length < 3) return null;
    const t = seq.slice(0, 3);
    if (!t.every((r) => hasScore(r) && margem(r) >= 4 && r.resultado === t[0].resultado)) return null;
    return { cor: t[0].resultado, key: 'NUM_DIFF4x3', nome: 'Diff ≥4 ×3', emoji: '🔢', strength: 85, tipo: 'num' };
  },
  function numViradaBaixa({ seq }) {
    if (seq.length < 2) return null;
    const [a, b] = seq;
    if (!hasScore(a) || !hasScore(b) || a.resultado !== b.resultado) return null;
    if (scoreOf(a) > 4 || scoreOf(b) > 4) return null;
    return { cor: opp(a.resultado), key: 'NUM_VIRADA_BAIXA', nome: 'Virada de baixos', emoji: '🔄', strength: 80, tipo: 'num' };
  },
  function numTendencia({ rows }) {
    const s = rows.slice(0, 8).filter(hasScore);
    if (s.length < 6) return null;
    const mj = s.reduce((a, r) => a + r.pj, 0) / s.length;
    const mb = s.reduce((a, r) => a + r.pb, 0) / s.length;
    const diff = mj - mb;
    if (Math.abs(diff) < 1.5) return null;
    return {
      cor: diff > 0 ? J : B, key: 'NUM_TENDENCIA',
      nome: `Tendência ${mj.toFixed(1)}×${mb.toFixed(1)}`, emoji: '📈',
      strength: Math.abs(diff) >= 2.2 ? 84 : 76, tipo: 'num'
    };
  },
  function numRangeSalto({ seq }) {
    if (seq.length < 2 || !hasScore(seq[0]) || !hasScore(seq[1])) return null;
    const [a, b] = seq;
    const ra = scoreRange(scoreOf(a)), rb = scoreRange(scoreOf(b));
    if (!ra || !rb) return null;
    if ((ra === 'MB' && rb === 'MA') || (ra === 'MA' && rb === 'MB')) {
      return { cor: opp(a.resultado), key: 'NUM_SALTO_RANGE', nome: `Salto ${scoreOf(b)}→${scoreOf(a)}`, emoji: '📐', strength: 81, tipo: 'num' };
    }
    return null;
  },
  function numScoreTrend3({ seq }) {
    if (seq.length < 3 || !seq.slice(0, 3).every(hasScore)) return null;
    const [a, b, c] = seq;
    if (a.resultado !== b.resultado || b.resultado !== c.resultado) return null;
    const sa = scoreOf(a), sb = scoreOf(b), sc = scoreOf(c);
    if (sa < sb && sb < sc) {
      return { cor: a.resultado, key: 'NUM_SCORE_TREND_3', nome: `Escala ascendente ${sa}→${sc}`, emoji: '📊', strength: 82, tipo: 'num' };
    }
    return null;
  },
  function numDoubleHigh({ seq }) {
    if (seq.length < 2 || !seq.slice(0, 2).every(hasScore)) return null;
    const [a, b] = seq;
    if (a.resultado !== b.resultado) return null;
    if (margem(a) >= 5 && margem(b) >= 5) {
      return { cor: a.resultado, key: 'NUM_DOUBLE_HIGH', nome: 'Dupla margem alta', emoji: '💪', strength: 84, tipo: 'num' };
    }
    return null;
  },
  function numMomentumShift({ seq }) {
    if (seq.length < 4 || !seq.slice(0, 4).every(hasScore)) return null;
    const [a, b, c, d] = seq;
    const sa = scoreOf(a), sb = scoreOf(b), sc = scoreOf(c), sd = scoreOf(d);
    if (sb - sa < 0 && sc - sb < 0 && sd - sc < 0) {
      return { cor: opp(a.resultado), key: 'MOMENTUM_SHIFT', nome: 'Mudança de momentum', emoji: '🔀', strength: 78, tipo: 'num' };
    }
    return null;
  },
  // ---- EMPATE ----
  function numPosEmpate({ rows, seq }) {
    if (!rows[0] || rows[0].resultado !== E || !seq.length) return null;
    return { cor: seq[0].resultado, key: 'NUM_POS_EMPATE', nome: 'Pós-empate', emoji: '🎯', strength: 74, tipo: 'num' };
  },
  function tieCascade({ rows }) {
    const ties = rows.slice(0, 3).filter((r) => r.resultado === E).length;
    if (ties < 2) return null;
    const pre = rows.find((r) => isCol(r.resultado));
    if (!pre) return null;
    return { cor: pre.resultado, key: 'TIE_CASCADE', nome: 'Cascata de empates', emoji: '🟡', strength: 76, tipo: 'num' };
  },
  function tieSingle({ rows, seq }) {
    if (!rows[0] || rows[0].resultado !== E) return null;
    if (!rows[1] || rows[1].resultado === E) return null;
    if (!seq.length) return null;
    return { cor: opp(seq[0].resultado), key: 'TIE_SINGLE', nome: 'Empate isolado', emoji: '🔀', strength: 77, tipo: 'num' };
  },
  function tieDoubleBack({ rows }) {
    if (rows.length < 3) return null;
    if (rows[0].resultado !== E || rows[1].resultado !== E) return null;
    if (!isCol(rows[2].resultado)) return null;
    return { cor: rows[2].resultado, key: 'TIE_DOUBLE_BACK', nome: 'Retorno pós-duplo empate', emoji: '🔙', strength: 78, tipo: 'num' };
  }
];

function runStrategies(rows) {
  const seq = rows.filter((r) => isCol(r.resultado));
  const ctx = { rows, seq };
  const out = [];
  for (const fn of STRATS) {
    try { const r = fn(ctx); if (r && isCol(r.cor)) out.push(r); } catch (_) {}
  }
  return out;
}

/* ============================ JANELA + BACKTEST ============================ */

// Janela de leitura: até 20 rodadas, mais recente primeiro, e PARA em qualquer buraco > windowGapMs.
// Usada IGUALMENTE pelo backtest e pelo live (v19 usava slice(-30) no live, atravessando quedas de API).
function windowAt(H, i) {
  const rows = [];
  for (let j = i; j >= 0 && rows.length < 20; j--) {
    if (rows.length && rows[rows.length - 1].t - H[j].t > CFG.windowGapMs) break;
    rows.push(H[j]);
  }
  return rows;
}

// Nível em que a entrada bate: 0 = sem gale, 1 = G1, 2 = G2, 3 = LOSS. null = ainda sem rodadas suficientes.
function evalDetail(H, i, cor) {
  for (let k = 1; k <= CFG.maxGale + 1; k++) {
    const idx = i + k;
    if (idx >= H.length) return null;
    if (H[idx].t - H[idx - 1].t > CFG.gapMs) return CFG.maxGale + 1; // buraco = entrada expirou
    if (H[idx].resultado === cor || H[idx].resultado === E) return k - 1;
  }
  return CFG.maxGale + 1;
}

function backtest() {
  const H = S.hist;
  const per = {};
  const ini = 10, fim = H.length - 1;
  if (fim - ini < 30) return { per, base: { r1: 0.80, r2: 0.90 } };
  let bn = 0, b1 = 0, b2 = 0;
  for (let i = ini; i < fim; i++) {
    const win = windowAt(H, i);
    if (win.length < CFG.warmupRounds) continue;
    for (const c of runStrategies(win)) {
      const lv = evalDetail(H, i, c.cor);
      if (lv === null) continue;
      const p = per[c.key] || (per[c.key] = { n: 0, w0: 0, w1: 0, w2: 0 });
      p.n++;
      if (lv <= 0) p.w0++;
      if (lv <= 1) p.w1++;
      if (lv <= 2) p.w2++;
      bn++; if (lv <= 1) b1++; if (lv <= 2) b2++;
    }
  }
  return {
    per,
    base: {
      r1: bn ? clamp(b1 / bn, 0.65, 0.92) : 0.80,
      r2: bn ? clamp(b2 / bn, 0.80, 0.97) : 0.90
    }
  };
}
function getStats(force = false) {
  if (force || !S.stats || S.novosDesdeStats >= 30) {
    S.stats = backtest();
    S.novosDesdeStats = 0; // FIX v20: contar rodadas NOVAS (hist travado em maxHist congelava o recálculo)
  }
  return S.stats;
}

/* ============================ ESTIMATIVA (substitui a "confiança" fixa 80–95) ============================ */

// Probabilidade histórica da estratégia bater até G1 (p1) e até G2 (p2).
// Encolhimento bayesiano para a média geral; combina backtest e sinais fechados (janela móvel).
// Observação: backtest e sinais ao vivo se sobrepõem em parte (mesmas rodadas) — aceitável para ranking.
function estimar(key, stats) {
  const p = stats.per[key] || { n: 0, w0: 0, w1: 0, w2: 0 };
  let n = p.n, w1 = p.w1, w2 = p.w2;
  for (const x of S.signals) {
    if (x.key !== key || !FECHADOS.has(x.status)) continue;
    n++;
    if (ATE_G1.has(x.status)) w1++;
    if (x.status !== 'LOSS') w2++;
  }
  const K = CFG.priorK;
  return {
    n,
    p1: (w1 + stats.base.r1 * K) / (n + K),
    p2: (w2 + stats.base.r2 * K) / (n + K)
  };
}

/* ============================ SUSPENSÃO (persistente) ============================ */

function isSuspended(key) {
  const u = SUSPENDED[key];
  if (!u) return false;
  if (Date.now() > u) { delete SUSPENDED[key]; dbStateSet('suspended', JSON.stringify(Object.entries(SUSPENDED))); return false; }
  return true;
}
function maybeSuspend(key) {
  const fechados = S.signals.filter((x) => x.key === key && FECHADOS.has(x.status));
  let motivo = null;
  const recent = fechados.slice(-CFG.suspendLossStreak);
  if (recent.length >= CFG.suspendLossStreak && recent.every((x) => x.status === 'LOSS')) {
    motivo = `${recent.length} LOSS seguidos`;
  }
  if (!motivo) {
    const win = fechados.slice(-CFG.suspendWindow);
    const losses = win.filter((x) => x.status === 'LOSS').length;
    if (win.length >= CFG.suspendWindow && losses >= CFG.suspendWindowLosses) motivo = `${losses} LOSS nos últimos ${win.length}`;
  }
  if (motivo) {
    SUSPENDED[key] = Date.now() + CFG.suspendMs;
    dbStateSet('suspended', JSON.stringify(Object.entries(SUSPENDED)));
    log('SUSPENSO', { key, motivo });
  }
}

/* ============================ TIER ============================ */
/* Tier 0 (mesa quente): rigoroso. Tier 1 (>= relaxMs sem sinal): relaxado.
   NÃO existe tier forçado: sem oportunidade, o bot fica calado. */

function idleMs() { return S.lastSignalAt ? Date.now() - S.lastSignalAt : Infinity; }
function tierAtual() { return idleMs() >= CFG.relaxMs ? 1 : 0; }

/* ============================ GATE ============================ */

function pendentes() { return S.signals.filter((s) => !FECHADOS.has(s.status)); }

function podeGerar() {
  if (!CFG.ativos) { R.ultimoMotivo = 'desativado'; return false; }
  const now = Date.now();
  const last = S.hist[S.hist.length - 1];
  if (!last) { R.ultimoMotivo = 'sem hist'; return false; }

  // API parada: não sinaliza em cima de dados velhos (era a causa dos sinais "forçados" com 33% de loss)
  if (now - last.t > CFG.freshMaxMs) {
    R.ultimoMotivo = `API parada ${Math.round((now - last.t) / 1000)}s`;
    S.apiWasDown = true;
    return false;
  }
  if (S.apiWasDown) {
    S.apiWasDown = false;
    S.skipNext = CFG.postGapSkip;
    log('API', `voltou — aquecendo ${CFG.warmupRounds} rodadas e pulando ${S.skipNext} sinal(is)`);
  }

  if (S.pauseUntil && now < S.pauseUntil) { R.ultimoMotivo = 'pausa de proteção'; return false; }
  if (DAILY.loss >= CFG.maxLossDia) { R.ultimoMotivo = 'stop de loss do dia'; return false; }
  if (pendentes().length >= CFG.maxPending) { R.ultimoMotivo = 'max pending'; return false; }
  if (S.lastSignalAt && now - S.lastSignalAt < CFG.minGapMs) {
    R.ultimoMotivo = `gap ${Math.ceil((CFG.minGapMs - (now - S.lastSignalAt)) / 1000)}s`;
    return false;
  }
  if (now - last.t < CFG.minSettledAgeMs) {
    R.ultimoMotivo = `rodada recente ${Math.ceil((CFG.minSettledAgeMs - (now - last.t)) / 1000)}s`;
    return false;
  }
  if (S.hist.length < CFG.minAmostra) { R.ultimoMotivo = `amostra ${S.hist.length}`; return false; }
  return true;
}

function liveHitRate(key) {
  let n = 0, w = 0;
  for (const x of S.signals) {
    if (x.key !== key || !FECHADOS.has(x.status)) continue;
    n++; if (x.status !== 'LOSS') w++;
  }
  return n >= 5 ? w / n : null;
}

/* ============================ GERAR SINAL ============================ */

async function tentarSinal() {
  if (!podeGerar()) return;

  const lastRound = S.hist[S.hist.length - 1];
  if (S.skipRoundId === lastRound.id) { R.ultimoMotivo = 'pulando rodada pós-retorno da API'; return; }

  const tier = tierAtual();
  R.tier = tier;
  const T = CFG.tiers[tier];

  const rows = windowAt(S.hist, S.hist.length - 1);
  if (rows.length < CFG.warmupRounds) {
    R.ultimoMotivo = `aquecendo ${rows.length}/${CFG.warmupRounds}`;
    return;
  }
  const stats = getStats();
  const seq = rows.filter((r) => isCol(r.resultado));
  const regime = detectRegime(seq);

  let cands = runStrategies(rows);
  if (!cands.length) { R.ultimoMotivo = 'sem estratégia'; return; }

  cands = cands.filter((c) => regimeFit(c, regime));
  const p1Min = stats.base.r1 + T.dP1;
  cands = cands
    .filter((c) => !CFG.blockKeys.includes(c.key) && !isSuspended(c.key))
    .map((c) => ({ ...c, est: estimar(c.key, stats) }))
    .filter((c) => {
      if (c.est.n < T.minN) return false;
      if (c.est.p1 < p1Min) return false;
      const lr = liveHitRate(c.key);
      if (lr !== null && lr < T.liveMin) return false;
      return true;
    });
  if (!cands.length) { R.ultimoMotivo = `tier${tier}: filtros (p1>=${(p1Min * 100).toFixed(0)}%, n>=${T.minN})`; return; }

  const porCor = {};
  for (const c of cands) (porCor[c.cor] || (porCor[c.cor] = [])).push(c);

  let melhor = null;
  for (const cor of Object.keys(porCor)) {
    const list = porCor[cor].slice().sort((a, b) => b.est.p1 - a.est.p1 || b.strength - a.strength);
    const top = list[0];
    if (!melhor || top.est.p1 > melhor.est.p1) melhor = { ...top, agree: list.length };
  }
  if (!melhor) { R.ultimoMotivo = 'sem candidato'; return; }

  // Primeiro sinal depois que a API volta: pula (1º sinal pós-queda teve 18% de loss; nos "forçados", 33%)
  if (S.skipNext > 0) {
    S.skipNext--;
    S.skipRoundId = lastRound.id;
    R.ultimoMotivo = 'pulando 1º sinal pós-retorno da API';
    log('SKIP', { key: melhor.key, rodada: lastRound.id });
    return;
  }

  const reservedId = S.nextId;
  const sinalPreliminar = {
    id: reservedId, cor: melhor.cor, key: melhor.key, nome: melhor.nome, emoji: melhor.emoji,
    conf: Math.round(melhor.est.p1 * 100), p1: melhor.est.p1, p2: melhor.est.p2,
    tipo: melhor.tipo, status: 'PENDENTE', tier,
    t: Date.now(), criadoEm: 0, agree: melhor.agree, // FIX v20: t preenchido antes do envio (antes mostrava 01:00:00)
    gale1MsgId: null, gale2MsgId: null, galeLevel: 0
  };

  const analisando = await tgSendRaw(fmtAnalisando());
  try {
    const envio = await tgSendRaw(fmtSinal(sinalPreliminar));
    if (!envio.ok) {
      log('SINAL', { motivo: 'telegram rejeitou sinal', id: reservedId });
      R.ultimoMotivo = 'telegram falhou';
      return;
    }
    const agora = Date.now();
    sinalPreliminar.t = agora;
    sinalPreliminar.criadoEm = agora;
    S.nextId++;
    S.signals.push(sinalPreliminar);
    if (S.signals.length > CFG.maxSignalsMem) S.signals = S.signals.slice(-CFG.maxSignalsMem + 50);
    S.lastSignalAt = agora;
    R.ultimoSinal = sinalPreliminar;
    R.ultimoMotivo = null;

    await dbSignalInsert(sinalPreliminar);
    await dbStateSet('nextId', String(S.nextId));
    await dbStateSet('lastSignalAt', String(agora));

    log('SINAL', {
      id: sinalPreliminar.id, cor: sinalPreliminar.cor, key: sinalPreliminar.key,
      p1: +(melhor.est.p1 * 100).toFixed(1), p2: +(melhor.est.p2 * 100).toFixed(1), n: melhor.est.n, tier
    });
  } finally {
    if (analisando.ok) await tgDelete(analisando.messageId);
  }
}

async function notificarGale(s, nivel) {
  if (nivel === 2 && s.gale1MsgId) {
    await tgDelete(s.gale1MsgId);
    s.gale1MsgId = null;
  }
  const r = await tgSendRaw(fmtGale(s, nivel));
  if (r.ok) {
    if (nivel === 1) s.gale1MsgId = r.messageId;
    else s.gale2MsgId = r.messageId;
    s.galeLevel = nivel;
  }
}

/* ============================ FECHAR ============================ */

async function fecharSinal(s, status, gale) {
  s.status = status;
  s.gale = gale;
  s.fechadoEm = Date.now();

  if (s.gale1MsgId) { await tgDelete(s.gale1MsgId); s.gale1MsgId = null; }
  if (s.gale2MsgId) { await tgDelete(s.gale2MsgId); s.gale2MsgId = null; }

  const bucket = status === 'GREEN' ? 'green' : status === 'G1' ? 'g1' : status === 'G2' ? 'g2'
    : status === 'EMPATE' ? 'empate' : status === 'EG1' ? 'eg1' : status === 'EG2' ? 'eg2' : 'loss';
  ALLTIME[bucket]++; ALLTIME.total++;
  DAILY[bucket]++; DAILY.total++;

  let msgProtecao = null;
  if (status === 'LOSS') {
    S.curStreak = 0;
    S.lossRun++;
    if (DAILY.loss >= CFG.maxLossDia) {
      msgProtecao = `🛑 <b>STOP DO DIA</b>\n${DAILY.loss} LOSS hoje. Sinais encerrados até 00h00. Respeite o stop da sua banca.`;
    } else if (S.lossRun >= CFG.lossPauseAfter) {
      S.pauseUntil = Date.now() + CFG.lossPauseMs;
      S.lossRun = 0;
      msgProtecao = `🛑 <b>PAUSA DE PROTEÇÃO</b>\n${CFG.lossPauseAfter} LOSS seguidos. Sinais pausados por ${Math.round(CFG.lossPauseMs / 60000)} min.`;
      await dbStateSet('pauseUntil', String(S.pauseUntil));
    }
  } else {
    S.curStreak++;
    S.lossRun = 0;
    if (S.curStreak > DAILY.bestStreak) DAILY.bestStreak = S.curStreak;
  }
  await dbStateSet('curStreak', String(S.curStreak));
  await dbStateSet('daily_v19', JSON.stringify(DAILY));

  await dbSignalUpdate(s);
  await tgSendRaw(fmtResult(s));
  await tgSendRaw(fmtHistorico());
  if (msgProtecao) await tgSendRaw(msgProtecao);
  maybeSuspend(s.key);
}

/* ============================ APURAÇÃO GALE 2 ============================ */
/* REGRA: gap > 7min = janela expirada → LOSS imediato */

async function apurar() {
  const now = Date.now();
  for (const s of S.signals) {
    if (FECHADOS.has(s.status)) continue;
    const after = S.hist.filter((r) => r.t > s.t).sort((a, b) => a.t - b.t);
    let decided = false;
    for (let k = 0; k <= CFG.maxGale && k < after.length; k++) {
      const r = after[k];
      const prevT = k === 0 ? s.t : after[k - 1].t;
      if (r.t - prevT > CFG.gapMs) {
        await fecharSinal(s, 'LOSS', k);
        decided = true; break;
      }
      if (r.resultado === s.cor || r.resultado === E) {
        const status = r.resultado === E ? (k === 0 ? 'EMPATE' : k === 1 ? 'EG1' : 'EG2') : (k === 0 ? 'GREEN' : k === 1 ? 'G1' : 'G2');
        await fecharSinal(s, status, k); decided = true; break;
      }
      if (k < CFG.maxGale && s.galeLevel < k + 1) await notificarGale(s, k + 1);
    }
    if (decided) continue;
    if (!after.length && now - s.t > CFG.gapMs) {
      await fecharSinal(s, 'LOSS', 0);
    } else if (after.length >= CFG.maxGale + 1) {
      await fecharSinal(s, 'LOSS', CFG.maxGale);
    } else if (now - s.t >= CFG.apuraMaxMs) {
      await fecharSinal(s, 'LOSS', s.galeLevel || 0);
    }
  }
}

/* ============================ SYNC ADAPTATIVO ============================ */
/* Tick a CADA 1 SEGUNDO. Com sinal pendente ou mesa quente, a API é consultada a cada 1s. */

function currentSyncMs() {
  if (pendentes().length > 0) return CFG.syncFastMs;
  const last = S.hist[S.hist.length - 1];
  if (last && Date.now() - last.t < 45000) return CFG.syncFastMs; // mesa quente
  return CFG.syncMs;
}

async function sync() {
  try {
    const rounds = await fetchRounds();
    let novos = 0, atualizados = 0;
    const byId = new Map(S.hist.map((r) => [r.id, r]));
    for (const r of rounds) {
      const previous = byId.get(r.id);
      if (!previous) {
        novos++; byId.set(r.id, r);
        await dbRoundUpsert(r);
      } else if (previous.t !== r.t || previous.resultado !== r.resultado || previous.pj !== r.pj || previous.pb !== r.pb) {
        Object.assign(previous, r); atualizados++;
        await dbRoundUpsert(r);
      }
    }
    S.hist = [...byId.values()].sort((a, b) => a.t - b.t || a.id.localeCompare(b.id));
    if (S.hist.length > CFG.maxHist) S.hist = S.hist.slice(-CFG.maxHist);
    S.seen = new Set(S.hist.map((r) => r.id));
    S.novosDesdeStats += novos;
    R.ultimaSync = new Date().toISOString();
    const newest = S.hist[S.hist.length - 1];
    if (newest) R.ultimaRodadaNova = new Date(newest.t).toISOString();

    if (newest && Date.now() - newest.t > CFG.staleAlertMs) {
      const mins = Math.floor((Date.now() - newest.t) / 60000);
      await tgAlert('API', `API BACBO sem rodadas novas há <b>${mins} min</b>.\nÚltima: ${R.ultimaRodadaNova}\nFonte: ${R.fonteAPI + 1}/${API_SOURCES.length}\nSinais pausados até a API normalizar.`);
    }
    if (novos || atualizados) log('SYNC', { novos, atualizados, total: S.hist.length, fonte: R.fonteAPI });
  } catch (e) {
    R.erroAPI = e.message;
    log('SYNC ERRO', e.message);
    await tgAlert('API', `Erro ao consultar API BACBO:\n<code>${e.message}</code>`);
  }
}

let lastSyncAt = 0;
async function tick() {
  if (busy || stopping) return;
  busy = true; lastTickMs = Date.now();
  try {
    await checkDailyReset();
    const now = Date.now();
    if (now - lastSyncAt >= currentSyncMs()) {
      await sync();
      lastSyncAt = Date.now();
    }
    await apurar();    // apura a cada 1s — gale nunca atrasa
    await tentarSinal();
  } catch (e) { log('TICK ERRO', e.message); }
  finally { busy = false; }
}

async function keepAlive() {
  const self = process.env.SELF_URL || process.env.RENDER_EXTERNAL_URL || '';
  if (self) { try { await axios.get(self.replace(/\/$/, '') + '/health', { timeout: 7000 }); } catch (_) {} }
}
function wakeCheck() {
  if (Date.now() - lastTickMs > 10000) {
    R.wakes++; R.ultimoWake = new Date().toISOString();
    log('WAKE', 'atraso'); tick().catch(() => {});
  }
}

/* ============================ EXPRESS ============================ */

const app = express();
app.disable('x-powered-by');
const corsOrigins = (process.env.CORS_ORIGINS || '').split(',').map((x) => x.trim()).filter(Boolean);
app.use(cors(corsOrigins.length ? { origin: corsOrigins } : { origin: false }));
app.use(express.json({ limit: '200kb' }));

function requireAdmin(req, res, next) {
  if (!ADMIN_TOKEN) return res.status(503).json({ erro: 'ADMIN_TOKEN não configurado' });
  const supplied = String(req.get('authorization') || '').replace(/^Bearer\s+/i, '');
  const a = Buffer.from(supplied);
  const b = Buffer.from(ADMIN_TOKEN);
  if (a.length !== b.length || !crypto.timingSafeEqual(a, b)) return res.status(401).json({ erro: 'não autorizado' });
  next();
}

app.get('/health', (req, res) => {
  const newest = S.hist[S.hist.length - 1];
  const apiStale = newest ? Date.now() - newest.t > CFG.staleAlertMs : true;
  res.json({
    ok: !R.erroAPI && Boolean(R.ultimaSync) && R.lockOk,
    versao: '20.0', deployId: DEPLOY_ID, maxGale: CFG.maxGale, lock: R.lockOk,
    tier: R.tier, fonteAPI: R.fonteAPI + 1, fontes: API_SOURCES.length,
    hist: S.hist.length, sinais: S.signals.length, pendentes: pendentes().length,
    diario: { ...DAILY, taxa: dailyTaxa(), semGale: dailySemGale(), lossPct: dailyLossPct() }, geral: ALLTIME,
    protecao: { pausaAte: S.pauseUntil > Date.now() ? new Date(S.pauseUntil).toISOString() : null, skipNext: S.skipNext },
    ultimaSync: R.ultimaSync, ultimaRodada: newest ? R.ultimaRodadaNova : null,
    apiStale, erroAPI: R.erroAPI, erroDB: R.erroDB,
    uptime: Math.round(process.uptime())
  });
});
app.get('/status', requireAdmin, (req, res) => {
  res.json({ motivo: R.ultimoMotivo, R, DAILY, ALLTIME, CFG, suspenso: Object.keys(SUSPENDED) });
});
app.get('/sinais', requireAdmin, (req, res) => {
  const n = Math.min(100, Math.max(1, parseInt(req.query.n, 10) || 20));
  res.json(S.signals.slice(-n).reverse());
});
app.get('/stats', requireAdmin, (req, res) => {
  const wins = dailyWins();
  const reais = DAILY.green + DAILY.g1 + DAILY.g2;
  const decididos = reais + DAILY.loss;
  const gw = ALLTIME.green + ALLTIME.g1 + ALLTIME.g2 + ALLTIME.empate + ALLTIME.eg1 + ALLTIME.eg2;
  const g0 = ALLTIME.green + ALLTIME.empate;
  const g01 = g0 + ALLTIME.g1 + ALLTIME.eg1;
  res.json({
    diario: {
      ...DAILY, wins, taxa: DAILY.total > 0 ? wins / DAILY.total : null,
      taxaReal: decididos > 0 ? reais / decididos : null,
      semGale: DAILY.total > 0 ? (DAILY.green + DAILY.empate) / DAILY.total : null,
      sequenciaAtual: S.curStreak
    },
    geral: {
      ...ALLTIME, wins: gw,
      taxa: ALLTIME.total > 0 ? gw / ALLTIME.total : null,
      semGale: ALLTIME.total > 0 ? g0 / ALLTIME.total : null,
      ateG1: ALLTIME.total > 0 ? g01 / ALLTIME.total : null,
      lossPct: ALLTIME.total > 0 ? ALLTIME.loss / ALLTIME.total : null
    }
  });
});
// Calibração: o número que o bot mostra (histórico até G1) bate com o resultado real?
// Obs.: sinais anteriores à v20 guardam a antiga nota 80–95 na coluna conf.
app.get('/calibracao', requireAdmin, (req, res) => {
  const defs = [['<76', 0, 75], ['76-79', 76, 79], ['80-83', 80, 83], ['84+', 84, 100]];
  const out = {};
  for (const [nome] of defs) out[nome] = { n: 0, ateG1: 0, ateG2: 0, loss: 0 };
  for (const s of S.signals) {
    if (!FECHADOS.has(s.status)) continue;
    const d = defs.find(([, a, b]) => s.conf >= a && s.conf <= b);
    if (!d) continue;
    const o = out[d[0]];
    o.n++;
    if (ATE_G1.has(s.status)) o.ateG1++;
    if (s.status !== 'LOSS') o.ateG2++; else o.loss++;
  }
  res.json(out);
});
app.get('/estrategias', requireAdmin, (req, res) => {
  const stats = getStats();
  const keys = new Set(Object.keys(stats.per));
  for (const s of S.signals) keys.add(s.key);
  const lista = [...keys].map((key) => {
    const e = estimar(key, stats);
    const h = histReal(key);
    return {
      key, n: e.n, p1: +(e.p1 * 100).toFixed(1), p2: +(e.p2 * 100).toFixed(1),
      sinaisFechados: h.n, loss: h.n - h.w,
      bloqueada: CFG.blockKeys.includes(key), suspensa: isSuspended(key)
    };
  }).sort((a, b) => b.p1 - a.p1);
  res.json({ base: stats.base, estrategias: lista });
});

/* ============================ START ============================ */

async function start() {
  for (const [name, value] of Object.entries({ BOT_TOKEN, CHAT_ID, ADMIN_TOKEN, DATABASE_URL })) {
    if (!value) throw new Error(`Variável obrigatória em falta: ${name}`);
  }
  if (!/^postgres(?:ql)?:\/\//i.test(DATABASE_URL)) throw new Error('DATABASE_URL inválido');
  log('BOOT', { versao: '20.0', deployId: DEPLOY_ID, fontes: API_SOURCES.length });
  await dbInit();
  if (!pool) throw new Error('Não foi possível inicializar PostgreSQL; arranque cancelado');

  const locked = await acquireLock();
  if (!locked) throw new Error('Outra instância do bot está ativa (advisory lock). Encerrando.');

  await dbLoadState();
  await sync();
  getStats(true);

  // Recupera PENDENTES com a regra de gap
  for (const s of S.signals) {
    if (s.status !== 'PENDENTE') continue;
    const after = S.hist.filter((r) => r.t > s.t).sort((a, b) => a.t - b.t);
    let consecutivasFalhas = 0, prevT = s.t;
    for (const r of after) {
      if (r.t - prevT > CFG.gapMs || r.resultado === s.cor || r.resultado === E) break;
      consecutivasFalhas++; prevT = r.t;
      if (consecutivasFalhas >= CFG.maxGale) break;
    }
    s.galeLevel = Math.min(consecutivasFalhas, CFG.maxGale);
  }

  server = app.listen(PORT, () => log('HTTP', `porta ${PORT}`));
  tickTimer = setInterval(() => tick().catch(() => {}), 1000);
  keepTimer = setInterval(() => { keepAlive().catch(() => {}); wakeCheck(); }, CFG.keepAliveMs);
  setTimeout(() => tick().catch(() => {}), 1500);

  process.on('SIGTERM', shutdown);
  process.on('SIGINT', shutdown);
}
async function shutdown() {
  if (stopping) return;
  stopping = true; log('SHUTDOWN', 'ok');
  clearInterval(tickTimer); clearInterval(keepTimer);
  if (server) await new Promise((resolve) => server.close(resolve));
  await releaseLock();
  if (pool) await pool.end().catch(() => {});
  process.exit(0);
}

start().catch((e) => { console.error(e); process.exit(1); });
