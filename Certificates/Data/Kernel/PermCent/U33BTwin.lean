module

public import Certificates.Data.Kernel.PermCent.CV
public import CFSG.GH74.KGroups.U33Inputs

public section

namespace CFSG.Certificates.Kernel.PkCV.U33B

open CFSG.GH74.KGroups.U33

@[expose] noncomputable def noOrdC : Bool :=
  (elemsC QP).all fun g => !orderIsP g 14 [2, 7] && !orderIsP g 21 [3, 7]

@[expose] noncomputable def e8atC (X : CV 28) (C : List (CV 28)) : Bool :=
  C.all fun Y => C.all fun Z =>
    decide (Y * Z ≠ Z * Y) || decide (Y ∈ ([1, X] : List (CV 28))) ||
      decide (Z ∈ ([1, X, Y, X * Y] : List (CV 28)))

@[expose] noncomputable def e8C : Bool :=
  (elemsC QP).all fun X => bif decide (X ^ 2 = 1) && decide (X ≠ 1) then
    e8atC X ((elemsC QP).filter (fun g => decide (g ^ 2 = 1 ∧ g * X = X * g))) else true

end CFSG.Certificates.Kernel.PkCV.U33B

end
