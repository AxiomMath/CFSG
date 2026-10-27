module

public import CFSG.LocalAnalysis.StandardType.UnitaryMatrixBridge
public import CFSG.LocalAnalysis.StandardType.UnitaryRepSmall

public section

namespace CFSG.StandardType

namespace UnitaryA3

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}

theorem eq_one_of_le_five (hn5 : n ≤ 5) {Γ : Subgroup (SU (unitaryInvolution F 2 f) n)}
    (h7 : HasOrderSevenData ↥Γ) (γ : ↥Γ) : γ = 1 :=
  UnitaryMatrix.eq_one_of_repHom_eq_one _ Γ
    (UnitaryRep.eq_one_of_card_le_five (unitaryInvolution F 2 f) h7
      (by simpa using hn5) UnitaryAlg.isUnit_antidiag (UnitaryMatrix.repHom _ n Γ)
      (UnitaryMatrix.repHom_form _ Γ) γ)

end UnitaryA3

end CFSG.StandardType
