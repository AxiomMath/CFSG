module

public import Certificates.Data.Kernel.F4PlanesRow

public section

namespace CFSG.KC.F4Planes

open CFSG.KC.F4Salt CFSG.KC.Loop CFSG.KC.F4Syl3

abbrev W4 : Type := Nat × Nat × Nat × Nat

@[expose] noncomputable def witPin (e : W4) : Bool :=
  eqS (wordS e.1 e.2.1) e.2.2.1 && eqS (mulS e.2.2.1 e.2.2.2) oneS

@[expose] noncomputable def witOne (U : Nat) (e : W4) : Bool :=
  strictB (mulS (mulS e.2.2.1 U) e.2.2.2) fun C =>
    eqS (mulS C U) (mulS U C) && !eqS C oneS && !eqS C U && !eqS C (mulS U U)

@[expose] noncomputable def witG (S : List Nat) (G4 G5 : Nat) (ww : List W4) (wk reps : List Nat) :
    Bool :=
  allL ww witPin && allN 48 fun k => Nat.blt (wk.getD k 0) (lenL ww) &&
    strictB (phiS S G4 G5 (reps.getD k 0)) fun U => witOne U (ww.getD (wk.getD k 0) (0, 0, 0, 0))

@[expose] noncomputable def witP (pS : List Nat) (ww : List W4) (wk reps : List Nat) : Bool :=
  strictB (pS.getD 0 0) fun S0 => strictB (pS.getD 1 0) fun S1 =>
    strictB (pS.getD 2 0) fun S2 => strictB (pS.getD 3 0) fun S3 =>
      strictB (pS.getD 4 0) fun G4 => strictB (pS.getD 5 0) fun G5 =>
        witG [S0, S1, S2, S3] G4 G5 ww wk reps

end CFSG.KC.F4Planes

end
