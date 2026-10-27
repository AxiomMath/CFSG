module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKNormOrthMat
public import CFSG.Open.StatedDefs
import CFSG.LieType.Universal.Spin.Forms

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

theorem s15k_norm_omminus_zmod2 {m : ℕ} (hm : 2 ≤ m)
    (M : Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2))
    (hM : ∀ g ∈ CFSG.MatrixModel.isometryCore (StatedQuadMinus m (ZMod 2) 1 1),
      M * g * M⁻¹ ∈ CFSG.MatrixModel.isometryCore (StatedQuadMinus m (ZMod 2) 1 1)) :
    M ∈ CFSG.MatrixModel.isometryCore (StatedQuadMinus m (ZMod 2) 1 1) := by
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite m (ZMod 2)
    hirr
  have hc := CFSG.LieType.Universal.Spin.coe_quadMinus m (ZMod 2) 1 1
  have h3 : 3 ≤ Fintype.card (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := by
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    omega
  rw [← hc] at hM ⊢
  exact s15k_norm_orth_matrix _ hQ h3 M hM

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
