module

public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs

public section

namespace CFSG.Sporadic.Schreier.TitsQT
open CFSG.Sporadic.Schreier.Tits CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def conjD0 : Array ℕ := titsDerivedArrs[0]!

@[expose] def conjD1 : Array ℕ := titsDerivedArrs[1]!

@[expose] def conjD0Inv : Array ℕ := invCand 1755 conjD0

@[expose] def conjD1Inv : Array ℕ := invCand 1755 conjD1

@[expose] def conjGArr : Array ℕ :=
  compA 1755 (compA 1755 (compA 1755 (compA 1755 conjD1Inv conjD0) conjD1Inv) conjD0) conjD0

@[expose] def conjGInvArr : Array ℕ :=
  compA 1755 (compA 1755 (compA 1755 (compA 1755 conjD0Inv conjD0Inv) conjD1) conjD0Inv) conjD1

@[expose] def conjXArr : Array ℕ := compA 1755 (compA 1755 conjGArr titsZArr) conjGInvArr

@[expose] def conjYArr : Array ℕ := compA 1755 (compA 1755 conjD0Inv titsZArr) conjD0

end CFSG.Sporadic.Schreier.TitsQT
