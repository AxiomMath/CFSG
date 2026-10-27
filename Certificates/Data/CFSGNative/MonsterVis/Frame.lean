module

public import Certificates.Data.CFSGNative.MonsterVis.Act
public import Certificates.Data.CFSGNative.MonsterVis.FrameData

public section

namespace CFSG.Monster.VisCert.Native

@[expose] def allFrom (p : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => true
  | lo, len + 1 => if p lo then allFrom p (lo + 1) len else false

@[expose] def countGo (p : Nat → Bool) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => countGo p n (if p n then acc + 1 else acc)

@[expose] def countBelow (p : Nat → Bool) (n : Nat) : Nat := countGo p n 0

@[expose] def parAll (n chunks : Nat) (p : Nat → Bool) : Bool :=
  let sz := n / chunks + 1
  ((List.range chunks).map fun j => Task.spawn fun _ => allFrom p (j * sz) sz).all Task.get

@[inline, expose] def rd8 (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat

@[inline, expose] def wr8 (b : ByteArray) (i x : Nat) : ByteArray := b.set! i (UInt8.ofNat x)

@[inline, expose] def rd32 (b : ByteArray) (i : Nat) : Nat :=
  let o := 4 * i
  (b.get! o).toNat ||| ((b.get! (o + 1)).toNat <<< 8) ||| ((b.get! (o + 2)).toNat <<< 16) |||
    ((b.get! (o + 3)).toNat <<< 24)

@[inline, expose] def wr32 (b : ByteArray) (i x : Nat) : ByteArray :=
  let o := 4 * i
  ((((b.set! o (UInt8.ofNat x)).set! (o + 1) (UInt8.ofNat (x >>> 8))).set! (o + 2)
    (UInt8.ofNat (x >>> 16))).set! (o + 3) (UInt8.ofNat (x >>> 24)))

@[expose] def zeros (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    b := b.push 0
  return b

@[expose] def fastTables (rows : Array Nat) : Array Nat := Id.run do
  let mut t : Array Nat := Array.mkEmpty 768
  for b in [0:3] do
    for x in [0:256] do
      t := t.push (actRows rows (x <<< (8 * b)))
  return t

@[inline, expose] def fastAct (t : Array Nat) (v : Nat) : Nat :=
  t[v &&& 255]! ^^^ t[256 + ((v >>> 8) &&& 255)]! ^^^ t[512 + ((v >>> 16) &&& 255)]!

structure FrameTables where
  klev : ByteArray
  klab : ByteArray
  kpar : ByteArray
  olab : ByteArray
  nlev : ByteArray
  nlab : ByteArray
  npar : ByteArray

@[expose] def kSearch (tabs : Array (Array Nat)) (seed : Nat) :
    ByteArray × ByteArray × ByteArray × Array Nat := Id.run do
  let n := 1 <<< 24
  let mut lev := wr8 (zeros n) seed 1
  let mut lab := zeros n
  let mut par := zeros (4 * n)
  let mut q : Array Nat := (Array.mkEmpty n).push seed
  let mut qh := 0
  for _ in [0:n] do
    if qh < q.size then
      let v := q[qh]!
      qh := qh + 1
      let lv := rd8 lev v
      for g in [0:tabs.size] do
        let w := fastAct tabs[g]! v
        if rd8 lev w == 0 then
          lev := wr8 lev w (lv + 1)
          lab := wr8 lab w g
          par := wr32 par w v
          q := q.push w
    else
      break
  return (lev, lab, par, q)

@[expose] def nSearch (tabs : Array (Array Nat)) (q : Array Nat) :
    ByteArray × ByteArray × ByteArray × ByteArray := Id.run do
  let n := 1 <<< 24
  let mut olab := zeros n
  let mut nlev := zeros n
  let mut nlab := zeros n
  let mut npar := zeros (4 * n)
  let mut nq : Array Nat := Array.mkEmpty q.size
  let mut nh := 0
  let mut norb := 0
  for qi in [0:q.size] do
    let v := q[qi]!
    if rd8 olab v == 0 then
      norb := norb + 1
      olab := wr8 olab v norb
      nlev := wr8 nlev v 1
      nq := nq.push v
      for _ in [0:n] do
        if nh < nq.size then
          let x := nq[nh]!
          nh := nh + 1
          let lx := rd8 nlev x
          for g in [1:tabs.size] do
            let y := fastAct tabs[g]! x
            if rd8 olab y == 0 then
              olab := wr8 olab y norb
              nlev := wr8 nlev y (lx + 1)
              nlab := wr8 nlab y g
              npar := wr32 npar y x
              nq := nq.push y
        else
          break
  return (olab, nlev, nlab, npar)

@[expose] def frameTables (_ : Unit := ()) : FrameTables :=
  let tabs := frameRows.map fastTables
  let (klev, klab, kpar, q) := kSearch tabs frameSeed
  let (olab, nlev, nlab, npar) := nSearch tabs q
  ⟨klev, klab, kpar, olab, nlev, nlab, npar⟩

@[inline, expose] def gimg (g v : Nat) : Nat := actRows frameRows[g]! v

@[inline, expose] def kOK (T : FrameTables) (v l : Nat) : Bool :=
  if l == 1 then v == frameSeed else
    let p := rd32 T.kpar v
    let g := rd8 T.klab v
    p < 2 ^ 24 && g < 15 && rd8 T.klev p + 1 == l && gimg g p == v

@[inline, expose] def closeOK (T : FrameTables) (v o : Nat) : Bool :=
  allFrom (fun j => rd8 T.klev (gimg j v) != 0 && rd8 T.olab (gimg j v) == o) 1 14

@[inline, expose] def nOK (T : FrameTables) (v o : Nat) : Bool :=
  let nl := rd8 T.nlev v
  if nl == 1 then v == frameReps[o - 1]! else
    let p := rd32 T.npar v
    let g := rd8 T.nlab v
    nl != 0 && p < 2 ^ 24 && 1 ≤ g && g < 15 && rd8 T.klev p != 0 && rd8 T.olab p == o &&
      rd8 T.nlev p + 1 == nl && gimg g p == v

@[inline, expose] def pointOK (T : FrameTables) (v : Nat) : Bool :=
  let l := rd8 T.klev v
  if l == 0 then true else
    let o := rd8 T.olab v
    kOK T v l && 1 ≤ o && o ≤ 6 && closeOK T v o && nOK T v o

@[expose] def frameCheck (T : FrameTables) (chunks : Nat) : Bool :=
  parAll (2 ^ 24) chunks (pointOK T) &&
    countBelow (fun v => rd8 T.klev v != 0) (2 ^ 24) == deltaCount &&
    allFrom (fun o => countBelow (fun v => rd8 T.klev v != 0 && rd8 T.olab v == o) (2 ^ 24) ==
      frameSizes[o - 1]!) 1 6 &&
    allFrom (fun o => frameReps[o - 1]! < 2 ^ 24 && rd8 T.klev frameReps[o - 1]! != 0 &&
      rd8 T.olab frameReps[o - 1]! == o) 1 6

@[expose] def frameCertOK (_ : Unit := ()) : Bool := frameCheck frameTables 8

end CFSG.Monster.VisCert.Native
