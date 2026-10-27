module

public import CFSG.Sporadic.J4.QTRankInvNative
public import CFSG.Sporadic.J4.QT2LocCntNative
public import CFSG.Quasithin.H13.NQCatJ4Native

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

set_option compiler.extract_closed false

@[expose] def burnsideJ4NP_natRows (R : Array V2) : Array Nat :=
  R.map fun v => v.lo.toNat + 2 ^ 64 * v.hi.toNat

@[expose] def burnsideJ4NP_rowFixOK (R : Array V2) (k : Nat) : Bool :=
  CFSG.Quasithin.H13.NQCat.Native.fixDimOK 112 (burnsideJ4NP_natRows (transposeRows R)) k

@[noinline, expose] def burnsideJ4NP_fixOKOf (T : Array (Array V2)) : Bool :=
  burnsideJ4NP_rowFixOK (etaRT T 1) 56 && burnsideJ4NP_rowFixOK (etaRT T 1131) 62

@[expose] def burnsideJ4NP_fixOK (_ : Unit := ()) : Bool :=
  burnsideJ4NP_fixOKOf (uTab (locMats ()) (locInvs ()))

@[expose] def burnsideJ4NP_classOfWith (x? : Option (Nat × Nat × List (Nat × Nat × Nat × Nat)))
    (im : List Nat) (c : Nat) : Option (Nat × Nat × Nat × Nat) :=
  match x? with
  | none => none
  | some x => x.2.2.find? fun y => im.contains (c ^^^ y.1)

@[expose] def burnsideJ4NP_classOf (c e : Nat) : Option (Nat × Nat × Nat × Nat) :=
  burnsideJ4NP_classOfWith (invData.find? (fun x => x.1 == e)) (imSet (tabE e)) c

@[expose] def burnsideJ4NP_is2APcWith (x? : Option (Nat × Nat × List (Nat × Nat × Nat × Nat)))
    (im : List Nat) (c e : Nat) : Bool :=
  if e = 0 then zMasks.contains c else
    match burnsideJ4NP_classOfWith x? im c with
    | none => false
    | some y => zMasks.contains y.2.2.1

@[expose] def burnsideJ4NP_is2APc (c e : Nat) : Bool :=
  if e = 0 then zMasks.contains c else
    match burnsideJ4NP_classOf c e with
    | none => false
    | some y => zMasks.contains y.2.2.1

end CFSG.ASVolI
