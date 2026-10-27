module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSCore
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitExcl
import CFSG.LocalAnalysis.StandardType.GGNbrLSideLinDich

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

theorem ggNbrLSideLinearData_holds (hDet : GGNbrLSideClsDet)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    GGNbrLSideLinearData := by
  refine ⟨fun ℓ n K _ _ _ _ hK => ?_, fun n K _ _ _ _ hK => ?_, fun n K _ _ _ _ hK => ?_⟩
  · refine ggNbrLSideLin_dich hDet hO ⟨.A, ℓ, n⟩ (d := ℓ + 1) hK ?_
    intro hn h9
    exact Or.inl ⟨hn, by show 6 ≤ ℓ; omega⟩
  · refine ggNbrLSideLin_dich hDet hO ⟨.D, 3, n⟩ (d := 4) hK ?_
    intro _ h9
    omega
  · refine ggNbrLSideLin_dich hDet hO ⟨.twD, 2, n⟩ (n := n * 2) (d := 2) (by rw [hK, pow_mul]) ?_
    intro _ h9
    omega

end CFSG.StandardType

end
