module

public import CFSG.Sporadic.Schreier.TitsInvCheckInputs
public import CFSG.Quasithin.Recognition.RuRank3TitsClsInputs

public section

namespace Certificates.TitsAschbacherStar

open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native

@[expose] def starWitIdx : ℕ := 8

@[expose] def starWit : Array ℕ := titsCNt.getD starWitIdx (idA 1755)

@[expose] def escapes (w u : Array ℕ) : Bool :=
  !commA w u && !eqA 1755 (compA 1755 (compA 1755 u w) u) w

@[expose] def starOK (u : Array ℕ) : Bool :=
  !eqA 1755 (compA 1755 u u) titsTArr || escapes starWit u

@[expose] def starCheck : Bool :=
  titsCNt.all fun c => starOK c && starOK (compA 1755 CFSG.Quasithin.RuRank3.titsAuxArr c)

end Certificates.TitsAschbacherStar
