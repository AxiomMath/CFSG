module

public import CFSG.Sporadic.J4.QT2ANative
public import CFSG.Sporadic.J4.QT2LocX0Data

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A CFSG.Sporadic.Th.Native

@[expose] def x0Words : List (List Int) := x0Strings.map w5

@[expose] def x0GenRows : Array (Array V2) := (x0Words.map wR).toArray

@[expose] def x0InvRows : Array (Array V2) := x0GenRows.map invRows

@[expose] def x0AllRows : Array (Array V2) := x0GenRows ++ x0InvRows

@[expose] def wfRows (M : Array V2) : Bool := M.size == 112 && M.all V2.wf

@[expose] def chkX0Gens : Bool :=
  x0Words.length == 8 && x0GenRows.size == 8 && x0InvRows.size == 8 &&
    eqRows (x0GenRows[0]!) (wR [1, 2, -3, 1, 2, -3]) &&
    (List.range 8).all fun i =>
      wfRows x0GenRows[i]! && wfRows x0InvRows[i]! &&
        eqRows (mulRows x0GenRows[i]! x0InvRows[i]!) idRows &&
        eqRows (mulRows x0InvRows[i]! x0GenRows[i]!) idRows &&
        eqRows (mulRows x0GenRows[i]! x0GenRows[0]!) (mulRows x0GenRows[0]! x0GenRows[i]!)

@[expose] def rowsHash (M : Array V2) : UInt64 := M.foldl (fun h r => mix (h ^^^ r.hash)) 0

structure MOrb where
  mats : Array (Array V2)
  par : Array Nat
  lab : Array Nat
  slots : ByteArray
  bits : Nat
deriving Inhabited

@[expose] def mfind (mats : Array (Array V2)) (slots : ByteArray) (bits : Nat) (k : Array V2) :
    Nat := Id.run do
  let mask := 2 ^ bits - 1
  let mut h := (rowsHash k).toNat &&& mask
  for _ in [0:2 ^ bits] do
    let e := rdU32 slots h
    if e == 0 then return 0
    if eqRows (mats[e - 1]?.getD #[]) k then return e
    h := (h + 1) &&& mask
  return 0

@[expose] def mslot (slots : ByteArray) (bits : Nat) (k : Array V2) : Nat := Id.run do
  let mask := 2 ^ bits - 1
  let mut h := (rowsHash k).toNat &&& mask
  for _ in [0:2 ^ bits] do
    if rdU32 slots h == 0 then return h
    h := (h + 1) &&& mask
  return h

@[inline, expose] def minsert (mats : Array (Array V2)) (slots : ByteArray) (bits : Nat)
    (k : Array V2) : ByteArray :=
  wrU32 slots (mslot slots bits k) (mats.size + 1)

@[expose] def obfs (step : Array V2 → Nat → Array V2) (nl : Nat) (w : Array V2) (cap bits : Nat) :
    MOrb := Id.run do
  let mut mats : Array (Array V2) := Array.mkEmpty cap
  let mut par : Array Nat := Array.mkEmpty cap
  let mut lab : Array Nat := Array.mkEmpty cap
  let mut slots := zeros (4 * 2 ^ bits)
  slots := minsert mats slots bits w
  mats := mats.push w
  par := par.push 0
  lab := lab.push 0
  for q in [0:cap] do
    if q < mats.size then
      let p := mats[q]!
      for g in [0:nl] do
        let y := step p g
        if mfind mats slots bits y == 0 && mats.size < cap then
          slots := minsert mats slots bits y
          mats := mats.push y
          par := par.push q
          lab := lab.push g
    else break
  return ⟨mats, par, lab, slots, bits⟩

@[inline, expose] def oOrbAt (step : Array V2 → Nat → Array V2) (nl : Nat) (O : MOrb) (q : Nat) :
    Bool :=
  let p := O.mats[q]!
  wfRows p && mfind O.mats O.slots O.bits p == q + 1 &&
    (List.range nl).all (fun g =>
      let y := step p g
      let e := mfind O.mats O.slots O.bits y
      e != 0 && e ≤ O.mats.size && eqRows (O.mats[e - 1]!) y) &&
    (q == 0 || (O.par[q]! < q && O.lab[q]! < nl &&
      eqRows (step O.mats[O.par[q]!]! O.lab[q]!) p))

@[expose] def oOrbOK (step : Array V2 → Nat → Array V2) (nl : Nat) (w : Array V2) (O : MOrb)
    (m : Nat) : Bool :=
  O.mats.size == m && O.par.size == m && O.lab.size == m && 0 < m && eqRows (O.mats[0]!) w &&
    (List.range m).all (oOrbAt step nl O)

@[inline, expose] def x0Step (M : Array V2) (g : Nat) : Array V2 := mulRows M (x0AllRows[g]!)

@[inline, expose] def x0CStep (M : Array V2) (g : Nat) : Array V2 :=
  mulRows (mulRows (x0AllRows[(g + 8) % 16]!) M) (x0AllRows[g]!)

@[expose] def x0Orb : MOrb := obfs x0Step 16 idRows 6720 14

@[expose] def chkX0Orb : Bool := oOrbOK x0Step 16 idRows x0Orb 6720

@[expose] def x0Eta (c : Nat) : Array V2 := etaE c

@[expose] def x0ConjT : MOrb := obfs x0CStep 16 (x0Eta 178) 84 8

@[expose] def x0ConjZ : MOrb := obfs x0CStep 16 (x0Eta 407) 7 5

@[expose] def chkX0Conj : Bool :=
  oOrbOK x0CStep 16 (x0Eta 178) x0ConjT 84 && oOrbOK x0CStep 16 (x0Eta 407) x0ConjZ 7

@[expose] def x0Invs : List (Array V2) :=
  x0Orb.mats.toList.filter fun M => !eqRows M idRows && eqRows (mulRows M M) idRows

@[expose] def chkX0Invs : Bool :=
  x0Invs.length == 91 &&
    x0Invs.all fun y => x0ConjT.mats.any (eqRows y) || x0ConjZ.mats.any (eqRows y)

@[expose] def x0Pts : List V2 := x0Orb.mats.toList.map fun M => frApply (frTable M) rootV

@[expose] def chkX0Pts : Bool :=
  let t0 := frTable (x0GenRows[0]!)
  x0Pts.eraseDups.length == 14 && x0Pts.all (fun p => (frApply t0 p).beq p) &&
    (x0Pts.filter fun p => p.beq rootV).length == 480

end CFSG.Sporadic.J4.QT2
