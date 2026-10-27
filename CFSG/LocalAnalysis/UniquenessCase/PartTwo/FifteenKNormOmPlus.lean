module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKNormOrthMat
public import CFSG.Open.StatedDefs
import CFSG.LieType.Universal.Spin.Forms

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

theorem s15k_norm_omplus_zmod2 {m : ℕ} (hm : 2 ≤ m)
    (M : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) (ZMod 2))
    (hM : ∀ g ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus m (ZMod 2)),
      M * g * M⁻¹ ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus m (ZMod 2))) :
    M ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus m (ZMod 2)) := by
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus m (ZMod 2)
  have hc := CFSG.LieType.Universal.Spin.coe_quadPlus m (ZMod 2)
  have h3 : 3 ≤ Fintype.card (Fin m ⊕ Fin m) := by
    rw [Fintype.card_sum, Fintype.card_fin]
    omega
  rw [← hc] at hM ⊢
  exact s15k_norm_orth_matrix _ hQ h3 M hM

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
