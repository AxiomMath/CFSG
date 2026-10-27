module

public import Certificates.Data.SmithL6Check

public section

namespace CFSG.SmithL6

open CFSG.SmithE (applyCols)

@[expose] def eaBits : List Nat := [0, 1, 2, 3, 16, 17, 18, 19]

@[expose] def eaSupp (c : Nat) : Bool := (List.range 20).all fun m => eaBits.contains m || !c.testBit m

@[expose] def eaChkC8 : Bool :=
  let A := tvCols 0
  let B := tvCols 31
  (List.range (2 ^ 20)).all fun c =>
    (applyCols A c == c && applyCols B c == c) == eaSupp c

@[expose] def eaChkW : Bool :=
  eaBits.all fun m => (List.range 1395).any fun i => wt i == 2 ^ m

@[expose] def eaI : List Nat :=
  (List.range 1953).filter fun p => tvImg p 0 == 0 && tvImg p 31 == 31

@[expose] def eaRestr (p : Nat) : List Nat :=
  let A := tvCols p
  eaBits.map fun m => applyCols A (2 ^ m)

@[expose] def eaChkF4 : Bool :=
  let R := eaI.map fun p => (p, eaRestr p)
  R.all fun a => R.all fun b => a.1 == b.1 || a.2 != b.2

@[expose] def eaRel (a b : Nat) : Nat :=
  if a = b then 0 else if tvImg a b = b then 1 else if tvImg a b = tvImg b a then 2 else 3

@[expose] def eaBase : List Nat := 0 :: 31 :: eaI

@[expose] def eaUniq (F : List Nat) (q : Nat) : Bool :=
  (List.range 1953).all fun q' => q' == q || F.any fun f => eaRel q f != eaRel q' f

@[expose] def eaF1 : List Nat := (List.range 1953).filter (eaUniq eaBase)

@[expose] def eaChkRig : Bool := (List.range 1953).all (eaUniq eaF1)

end CFSG.SmithL6
