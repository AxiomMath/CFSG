module

public import Certificates.Data.CFSGNative.MonsterVis.Frame
public import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.Monster.Existence.CoPair.Native

open CFSG.Monster.VisCert.Native

set_option compiler.extract_closed false

@[inline, expose] def letterRows (l : Nat) : Array Nat :=
  (CFSG.Monster.B.Co2.Native.genRecords[l]!).matrix

@[expose] def actLetters : List Nat → Nat → Nat
  | [], v => v
  | l :: w, v => actLetters w (actRows (letterRows l) v)

@[expose] def xWordN (_ : Unit := ()) : List Nat :=
  [5, 16, 1, 15, 5, 16, 1, 15, 5, 16, 1, 15, 5, 16, 1, 15, 5, 16, 1, 15]

@[expose] def yWordN (_ : Unit := ()) : List Nat :=
  [23, 1, 23, 1, 23, 1, 16, 6, 19, 23, 16, 6, 19, 23, 16, 6, 19, 23, 16, 6,
    19, 23, 23, 1]

@[expose] def actXY : List Nat → Nat → Nat
  | [], v => v
  | g :: w, v => actXY w (actLetters (if g == 0 then xWordN else yWordN) v)

@[inline, expose] def genXY (g v : Nat) : Nat := actXY [g] v

structure OrbTables where
  lev : ByteArray
  lab : ByteArray
  par : ByteArray

@[expose] def orbSearch (seed : Nat) : OrbTables := Id.run do
  let n := 1 <<< 24
  let mut lev := wr8 (zeros n) seed 1
  let mut lab := zeros n
  let mut par := zeros (4 * n)
  let mut q : Array Nat := (Array.mkEmpty 65536).push seed
  let mut qh := 0
  for _ in [0:n] do
    if qh < q.size then
      let v := q[qh]!
      qh := qh + 1
      let lv := rd8 lev v
      for g in [0:2] do
        let w := genXY g v
        if w < n && rd8 lev w == 0 then
          lev := wr8 lev w (lv + 1)
          lab := wr8 lab w g
          par := wr32 par w v
          q := q.push w
    else
      break
  return ⟨lev, lab, par⟩

@[inline, expose] def orbPoint (seed : Nat) (lev par lab : Nat → Nat) (v : Nat) : Bool :=
  let l := lev v
  if l == 0 then true else
    (if l == 1 then v == seed else
      let p := par v
      let g := lab v
      p < 2 ^ 24 && g < 2 && lev p + 1 == l && genXY g p == v) &&
    genXY 0 v < 2 ^ 24 && lev (genXY 0 v) != 0 && genXY 1 v < 2 ^ 24 && lev (genXY 1 v) != 0

@[expose] def orbCheck (seed N : Nat) (T : OrbTables) (chunks : Nat) : Bool :=
  seed < 2 ^ 24 && rd8 T.lev seed == 1 &&
    parAll (2 ^ 24) chunks (orbPoint seed (rd8 T.lev) (rd32 T.par) (rd8 T.lab)) &&
    countBelow (fun v => rd8 T.lev v != 0) (2 ^ 24) == N

@[inline, expose] def rd16 (b : ByteArray) (i : Nat) : Nat :=
  (b.get! (2 * i)).toNat ||| ((b.get! (2 * i + 1)).toNat <<< 8)

@[inline, expose] def wr16 (b : ByteArray) (i x : Nat) : ByteArray :=
  (b.set! (2 * i) (UInt8.ofNat x)).set! (2 * i + 1) (UInt8.ofNat (x >>> 8))

structure EqTables where
  pl : ByteArray
  rep : Array Nat

@[expose] def eqSearch (a b : List Nat) (σa σb : Nat → Nat) (n seed j0 : Nat) : EqTables :=
  Id.run do
  let sz := 1 <<< 24
  let mut pl := wr16 (zeros (2 * sz)) seed (j0 + 1)
  let mut q : Array Nat := (Array.mkEmpty 65536).push seed
  let mut qh := 0
  for _ in [0:sz] do
    if qh < q.size then
      let v := q[qh]!
      qh := qh + 1
      let j := rd16 pl v - 1
      let va := actXY a v
      if va < sz && rd16 pl va == 0 then
        pl := wr16 pl va (σa j + 1)
        q := q.push va
      let vb := actXY b v
      if vb < sz && rd16 pl vb == 0 then
        pl := wr16 pl vb (σb j + 1)
        q := q.push vb
    else
      break
  let mut rep : Array Nat := Array.replicate n sz
  for v in q do
    let j := rd16 pl v - 1
    if j < n && rep[j]! == sz then
      rep := rep.set! j v
  return ⟨pl, rep⟩

@[inline, expose] def eqPoint (a b : List Nat) (σa σb : Nat → Nat) (n : Nat) (pl : Nat → Nat)
    (v : Nat) : Bool :=
  let q := pl v
  if q == 0 then true else
    1 ≤ q && q ≤ n && actXY a v < 2 ^ 24 && actXY b v < 2 ^ 24 &&
      pl (actXY a v) == σa (q - 1) + 1 && pl (actXY b v) == σb (q - 1) + 1

@[expose] def eqCheck (a b : List Nat) (σa σb : Nat → Nat) (n : Nat) (T : EqTables)
    (chunks : Nat) : Bool :=
  parAll (2 ^ 24) chunks (eqPoint a b σa σb n (rd16 T.pl)) &&
    allFrom (fun j => T.rep[j]! < 2 ^ 24 && rd16 T.pl T.rep[j]! == j + 1) 0 n

end CFSG.Monster.Existence.CoPair.Native
