module

public import Certificates.Data.CFSGNative.YGroups.DCE.PermB
public import Certificates.Data.CFSGNative.YGroups.DCE.Omega

public section

namespace CFSG.YGroups.DCE

open CFSG.Monster.B.Co2.Native

@[inline, expose] def byteOf (h i : Nat) : UInt8 := UInt8.ofNat (h >>> (8 * i))

@[inline] def tabU8 (b : ByteArray) (i : USize) : UInt8 :=
  if h : i.toNat < b.size then b.uget i h else 0

@[inline] def tabU32 (b : ByteArray) (i : USize) : UInt32 :=
  (tabU8 b i).toUInt32 ||| ((tabU8 b (i + 1)).toUInt32 <<< 8) |||
    ((tabU8 b (i + 2)).toUInt32 <<< 16) ||| ((tabU8 b (i + 3)).toUInt32 <<< 24)

@[inline] def tabU64 (b : ByteArray) (i : USize) : UInt64 :=
  (tabU32 b i).toUInt64 ||| ((tabU32 b (i + 4)).toUInt64 <<< 32)

@[expose] def slotSet (tab : ByteArray) (s h v : Nat) : ByteArray := Id.run do
  let mut t := tab
  for i in [0:8] do
    t := t.set! (12 * s + i) (UInt8.ofNat (h >>> (8 * i)))
  for i in [0:4] do
    t := t.set! (12 * s + 8 + i) (UInt8.ofNat ((v + 1) >>> (8 * i)))
  return t

@[expose] def tabGo (tab : ByteArray) (key : UInt64) (mask : USize) : Nat → USize → Nat
  | 0, _ => 0
  | fuel + 1, s =>
    let v := tabU32 tab (12 * s + 8)
    if v == 0 then 0
    else if tabU64 tab (12 * s) == key then v.toNat
    else tabGo tab key mask fuel ((s + 1) &&& mask)

@[expose] def tabGet (tab : ByteArray) (bits h : Nat) : Nat :=
  let mask : USize := (1 <<< bits.toUSize) - 1
  let key := h.toUInt64
  tabGo tab key mask (mask.toNat + 1) (key.toUSize &&& mask)

def tabPutGo (tab : ByteArray) (h v : Nat) (mask : USize) : Nat → USize → ByteArray
  | 0, _ => tab
  | fuel + 1, s =>
    if tabU32 tab (12 * s + 8) == 0 then slotSet tab s.toNat h v
    else tabPutGo tab h v mask fuel ((s + 1) &&& mask)

def tabPut (tab : ByteArray) (bits h v : Nat) : ByteArray :=
  let mask : USize := (1 <<< bits.toUSize) - 1
  tabPutGo tab h v mask (mask.toNat + 1) (h.toUInt64.toUSize &&& mask)

@[expose] def zeroBytes (k : Nat) : ByteArray := Id.run do
  let blk := ByteArray.mk (Array.replicate 4096 0)
  let mut b : ByteArray := ByteArray.emptyWithCapacity k
  for _ in [0:k / 4096] do
    b := b ++ blk
  for _ in [0:k % 4096] do
    b := b.push 0
  return b

@[inline, expose] def push32 (b : ByteArray) (x : Nat) : ByteArray :=
  (((b.push (byteOf x 0)).push (byteOf x 1)).push (byteOf x 2)).push (byteOf x 3)

structure BigOmega where
  n : Nat
  m : Nat
  X0 : Array Nat
  tg : Array ByteArray
  N : Nat
  par : ByteArray
  lab : ByteArray
  R : Array Nat
  bits : Nat
  tab : ByteArray

namespace BigOmega

@[inline, expose] def parAt (O : BigOmega) (p : Nat) : Nat :=
  (O.par.get! (4 * p)).toNat + 256 * (O.par.get! (4 * p + 1)).toNat +
    65536 * (O.par.get! (4 * p + 2)).toNat + 16777216 * (O.par.get! (4 * p + 3)).toNat

@[inline, expose] def labAt (O : BigOmega) (p : Nat) : Nat := (O.lab.get! p).toNat

@[expose] def rowAux (O : BigOmega) : Nat → Nat → Array Nat
  | 0, _ => O.X0
  | fuel + 1, p =>
    if p = 0 then O.X0
    else
      let σ := O.tg[O.labAt p]!
      (O.rowAux fuel (O.parAt p)).map fun x => bget σ x

@[expose] def row (O : BigOmega) (p : Nat) : Array Nat := O.rowAux p p

@[expose] def rowHash (O : BigOmega) (p : Nat) : Nat :=
  let r := O.row p
  sumMod O.m fun k => O.R[r[k]!]!

@[expose] def imgHash (O : BigOmega) (σ : ByteArray) (p : Nat) : Nat :=
  let r := O.row p
  sumMod O.m fun k => O.R[bget σ r[k]!]!

@[expose] def find (O : BigOmega) (h : Nat) : Nat :=
  let v := tabGet O.tab O.bits h
  if v == 0 then O.N else v - 1

@[expose] def act (O : BigOmega) (σ : ByteArray) (p : Nat) : Nat := O.find (O.imgHash σ p)

end BigOmega

@[expose] def segSize (_ : Unit := ()) : Nat := 65536

@[inline, expose] def segPar (ps : Array ByteArray) (pc : ByteArray) (p : Nat) : Nat :=
  let b := if p / segSize < ps.size then ps[p / segSize]! else pc
  let o := 4 * (p % segSize)
  (b.get! o).toNat + 256 * (b.get! (o + 1)).toNat + 65536 * (b.get! (o + 2)).toNat +
    16777216 * (b.get! (o + 3)).toNat

@[inline, expose] def segLab (ls : Array ByteArray) (lc : ByteArray) (p : Nat) : Nat :=
  let b := if p / segSize < ls.size then ls[p / segSize]! else lc
  (b.get! (p % segSize)).toNat

structure BfsCfg where
  n : Nat
  tg : Array ByteArray
  X0 : Array Nat
  R : Array Nat
  Rs : Array (Array Nat)
  cap : Nat
  bits : Nat
  tasks : Nat
  chunk : Nat
  minPar : Nat

@[expose] def BfsCfg.make (n : Nat) (tg : Array ByteArray) (X0 : Array Nat)
    (cap bits tasks chunk minPar : Nat) : BfsCfg :=
  let R := weights n
  { n, tg, X0, R, Rs := tg.map fun σ => (Array.range n).map fun x => R[bget σ x]!, cap, bits,
    tasks, chunk, minPar }

@[expose] def bfsRows (cfg : BfsCfg) (ps : Array ByteArray) (pc : ByteArray)
    (ls : Array ByteArray) (lc : ByteArray) (a b : Nat) (stIdx : Array Nat)
    (stRow : Array (Array Nat)) : Array (Array Nat) × Array Nat × Array (Array Nat) := Id.run do
  let mut stIdx := stIdx
  let mut stRow := stRow
  let mut rows : Array (Array Nat) := Array.emptyWithCapacity (b - a)
  for h in [a:b] do
    let mut up : Array Nat := #[h]
    let mut q := h
    for _ in [0:h] do
      if q == 0 then break
      q := segPar ps pc q
      up := up.push q
    let d := up.size
    let mut j := 0
    for _ in [0:d] do
      if j < stIdx.size && stIdx[j]! == up[d - 1 - j]! then j := j + 1 else break
    stIdx := stIdx.extract 0 j
    stRow := stRow.extract 0 j
    for i in [j:d] do
      let c := up[d - 1 - i]!
      if i == 0 then
        stRow := stRow.push cfg.X0
      else
        let σ := cfg.tg[segLab ls lc c]!
        stRow := stRow.push (stRow[i - 1]!.map fun x => bget σ x)
      stIdx := stIdx.push c
    rows := rows.push stRow[d - 1]!
  return (rows, stIdx, stRow)

@[expose] def bfsRange (cfg : BfsCfg) (ps : Array ByteArray) (pc : ByteArray)
    (ls : Array ByteArray) (lc : ByteArray) (a b : Nat) : Array Nat := Id.run do
  let g := cfg.tg.size
  let blk := 256
  let mut out : Array Nat := Array.replicate ((b - a) * g) 0
  let mut stIdx : Array Nat := #[]
  let mut stRow : Array (Array Nat) := #[]
  let mut lo := a
  for _ in [0:(b - a) / blk + 1] do
    if lo < b then
      let hi := min b (lo + blk)
      let (rows, stIdx', stRow') := bfsRows cfg ps pc ls lc lo hi stIdx stRow
      stIdx := stIdx'
      stRow := stRow'
      for l in [0:g] do
        let Rl := cfg.Rs[l]!
        for i in [0:rows.size] do
          out := out.set! ((lo + i - a) * g + l) (rows[i]!.foldl (fun s x => s + Rl[x]!) 0)
      lo := hi
  return out

structure BfsSt where
  parSegs : Array ByteArray
  labSegs : Array ByteArray
  parCur : ByteArray
  labCur : ByteArray
  tab : ByteArray
  cnt : Nat
  head : Nat
  truncated : Bool
  pend : Array (Nat × Task (Array Nat))
  ahead : Nat

@[expose] def bfsSpawn (cfg : BfsCfg) (ps : Array ByteArray) (pc : ByteArray)
    (ls : Array ByteArray) (lc : ByteArray) (a b : Nat) : Array (Nat × Task (Array Nat)) :=
  let len := b - a
  let T := if len < cfg.minPar then 1 else max 1 cfg.tasks
  let sz := (len + T - 1) / T
  (Array.range T).map fun t =>
    (a + t * sz, Task.spawn fun _ =>
      bfsRange cfg ps pc ls lc (a + t * sz) (min b (a + (t + 1) * sz)))

@[expose] def bfsChunkEnd (cfg : BfsCfg) (cnt a : Nat) : Nat :=
  min cnt (a + min (max 1 cfg.chunk) ((cnt - a) / 4 + 1))

@[expose] def bfsStep (cfg : BfsCfg) (st : BfsSt) : BfsSt :=
  match st with
  | ⟨parSegs, labSegs, parCur, labCur, tab, cnt, head, truncated, pend, ahead⟩ =>
    let g := cfg.tg.size
    let hi0 := bfsChunkEnd cfg cnt head
    let cur : Array (Nat × Task (Array Nat)) × Nat :=
      if pend.isEmpty then (bfsSpawn cfg parSegs parCur labSegs labCur head hi0, hi0)
      else (pend, ahead)
    let hi := cur.2
    let hi' := bfsChunkEnd cfg cnt hi
    let next : Array (Nat × Task (Array Nat)) :=
      if hi < hi' then bfsSpawn cfg parSegs parCur labSegs labCur hi hi' else #[]
    Id.run do
      let mut parSegs := parSegs
      let mut labSegs := labSegs
      let mut parCur := parCur
      let mut labCur := labCur
      let mut tab := tab
      let mut cnt := cnt
      let mut truncated := truncated
      for t in [0:cur.1.size] do
        let a := cur.1[t]!.1
        let res := cur.1[t]!.2.get
        for hh in [0:res.size / g] do
          for l in [0:g] do
            let hv := res[hh * g + l]!
            if tabGet tab cfg.bits hv == 0 then
              if cnt < cfg.cap then
                tab := tabPut tab cfg.bits hv cnt
                parCur := push32 parCur (a + hh)
                labCur := labCur.push (UInt8.ofNat l)
                cnt := cnt + 1
                if cnt % segSize == 0 then
                  parSegs := parSegs.push parCur
                  labSegs := labSegs.push labCur
                  parCur := ByteArray.emptyWithCapacity (4 * segSize)
                  labCur := ByteArray.emptyWithCapacity segSize
              else
                truncated := true
      return ⟨parSegs, labSegs, parCur, labCur, tab, cnt, hi, truncated, next,
        if next.isEmpty then hi else hi'⟩

@[expose] def bfsInit (cfg : BfsCfg) : BfsSt :=
  ⟨#[], #[], push32 (ByteArray.emptyWithCapacity (4 * segSize)) 0,
    (ByteArray.emptyWithCapacity segSize).push 0,
    tabPut (zeroBytes (12 * 2 ^ cfg.bits)) cfg.bits (cfg.X0.foldl (fun s x => s + cfg.R[x]!) 0) 0,
    1, 0, false, #[], 0⟩

@[expose] def bfsFinish (cfg : BfsCfg) (st : BfsSt) : BigOmega :=
  { n := cfg.n, m := cfg.X0.size, X0 := cfg.X0, tg := cfg.tg, N := st.cnt,
    par := (st.parSegs.foldl (fun (b : ByteArray) s => b ++ s)
      (ByteArray.emptyWithCapacity (4 * st.cnt))) ++ st.parCur,
    lab := (st.labSegs.foldl (fun (b : ByteArray) s => b ++ s)
      (ByteArray.emptyWithCapacity st.cnt)) ++ st.labCur,
    R := cfg.R, bits := cfg.bits, tab := st.tab }

@[expose] def mkBigOmegaAux (n : Nat) (tg : Array ByteArray) (X0 : Array Nat) (cap bits : Nat)
    (tasks : Nat := 32) (chunk : Nat := 262144) (minPar : Nat := 256) : BigOmega × Bool :=
  Id.run do
    let cfg := BfsCfg.make n tg X0 cap bits tasks chunk minPar
    let mut st := bfsInit cfg
    for _ in [0:cap + 1] do
      if st.head < st.cnt then
        st := bfsStep cfg st
      else
        break
    return (bfsFinish cfg st, st.truncated)

@[expose] def mkBigOmega (n : Nat) (tg : Array ByteArray) (X0 : Array Nat) (cap bits : Nat) :
    BigOmega :=
  (mkBigOmegaAux n tg X0 cap bits).1

@[expose] def u32Entry (b : ByteArray) (x : Nat) : Nat :=
  (b.get! (4 * x)).toNat + 256 * (b.get! (4 * x + 1)).toNat +
    65536 * (b.get! (4 * x + 2)).toNat + 16777216 * (b.get! (4 * x + 3)).toNat

@[expose] def u32fill (f : Nat → Nat) : Nat → Nat → ByteArray → ByteArray
  | 0, _, b => b
  | k + 1, x, b => u32fill f k (x + 1) (push32 b (f x))

@[expose] def u32chunk (f : Nat → Nat) (lo hi : Nat) : ByteArray :=
  u32fill f (hi - lo) lo (ByteArray.emptyWithCapacity (4 * (hi - lo)))

def runs (xs : Array Nat) : Array Nat × Array Nat := Id.run do
  let mut ps : Array Nat := #[]
  let mut pos : Array Nat := Array.emptyWithCapacity xs.size
  let mut last := 0
  for x in xs do
    if ps.isEmpty || last != x then
      ps := ps.push x
      last := x
    pos := pos.push (ps.size - 1)
  return (ps, pos)

namespace BigOmega

@[expose] def rowVia (O : BigOmega) (P : Array (Array Nat)) (ps pos : Array Nat) (i q : Nat) :
    Array Nat :=
  if q < O.N ∧ q ≠ 0 ∧ pos[i]! < ps.size ∧ ps[pos[i]!]! = O.parAt q then
    (P[pos[i]!]!).map fun x => bget (O.tg[O.labAt q]!) x
  else O.row q

@[expose] def rowsFor (O : BigOmega) : Nat → Array Nat → Array (Array Nat)
  | 0, qs => qs.map O.row
  | f + 1, qs =>
    if qs.size ≤ 2 then qs.map O.row
    else
      let rp := runs (qs.map O.parAt)
      let P := O.rowsFor f rp.1
      (Array.range qs.size).map fun i => O.rowVia P rp.1 rp.2 i qs[i]!

@[expose] def actTabs (O : BigOmega) (σ : ByteArray) : Array (Array Nat) :=
  O.tg.map fun τ => (Array.range O.n).map fun x => O.R[bget σ (bget τ x)]!

@[expose] def hashVia (O : BigOmega) (T : Array (Array Nat)) (P : Array (Array Nat))
    (pos : Array Nat) (i p : Nat) : Nat :=
  let Tl := T[O.labAt p]!
  (P[pos[i]!]!).foldl (fun s x => s + Tl[x]!) 0

@[expose] def actVia (O : BigOmega) (σ : ByteArray) (ps pos : Array Nat) (i p h : Nat) : Nat :=
  if p < O.N ∧ p ≠ 0 ∧ pos[i]! < ps.size ∧ ps[pos[i]!]! = O.parAt p then O.find h
  else O.act σ p

def byLabel (O : BigOmega) (a len : Nat) : Array Nat × Array Nat := Id.run do
  let g := O.tg.size
  let mut cnts : Array Nat := Array.replicate (g + 2) 0
  for i in [0:len] do
    let l := min (O.labAt (a + i)) g
    cnts := cnts.set! (l + 1) (cnts[l + 1]! + 1)
  for l in [0:g + 1] do
    cnts := cnts.set! (l + 1) (cnts[l + 1]! + cnts[l]!)
  let mut order : Array Nat := Array.replicate len 0
  let mut inv : Array Nat := Array.replicate len 0
  for i in [0:len] do
    let l := min (O.labAt (a + i)) g
    let j := cnts[l]!
    order := order.set! j i
    inv := inv.set! i j
    cnts := cnts.set! l (j + 1)
  return (order, inv)

@[expose] def actChunk (O : BigOmega) (T : Array (Array Nat)) (σ : ByteArray) (a b : Nat) :
    ByteArray :=
  let rp := runs ((Array.range (b - a)).map fun i => O.parAt (a + i))
  let P := O.rowsFor 64 rp.1
  let ord := O.byLabel a (b - a)
  let hs := ord.1.map fun i => O.hashVia T P rp.2 i (a + i)
  u32chunk (fun p =>
    O.actVia σ rp.1 rp.2 (p - a) p
      (if ord.2[p - a]! < ord.1.size ∧ ord.1[ord.2[p - a]!]! = p - a then hs[ord.2[p - a]!]!
       else O.hashVia T P rp.2 (p - a) p)) a b

@[expose] def actAll (O : BigOmega) (σ : ByteArray) (chunk : Nat := 16384) : ByteArray :=
  let T := O.actTabs σ
  let k := O.N / chunk + 1
  let parts := (List.range k).map fun t =>
    Task.spawn fun _ => O.actChunk T σ (min O.N (t * chunk)) (min O.N ((t + 1) * chunk))
  parts.foldl (fun acc t => acc ++ t.get) (ByteArray.emptyWithCapacity (4 * O.N))

end BigOmega

@[expose] def mapsIntoB (X0 : Array Nat) (σ : ByteArray) : Bool :=
  allLt X0.size fun a => X0.contains (bget σ X0[a]!)

@[expose] def findOK (O : BigOmega) : Bool :=
  let A := O.actAll (bid O.n)
  allLt O.N fun p => u32Entry A p == p

@[expose] def bigOK (O : BigOmega) (letters : Array ByteArray) (fix : List Nat) : Bool :=
  O.m == O.X0.size && 0 < O.N && decide (O.N < 4294967296) && decide (O.n ≤ 65536) &&
    O.par.size == 4 * O.N && O.lab.size == O.N && O.R.size == O.n &&
    O.tab.size == 12 * 2 ^ O.bits &&
    O.tg.all (fun t => t.size == 2 * O.n && allLt O.n fun x => decide (bget t x < O.n)) &&
    rowNodup O.n O.X0 &&
    fix.all (fun l => decide (l < letters.size) && mapsIntoB O.X0 letters[l]!) &&
    allLt O.N (fun p => p == 0 || (decide (O.parAt p < p) && decide (O.labAt p < O.tg.size))) &&
    findOK O

end CFSG.YGroups.DCE
