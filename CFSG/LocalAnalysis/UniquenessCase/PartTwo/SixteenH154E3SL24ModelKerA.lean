module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24Model

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.GH74.KGroups

lemma s16h_orth3Act_radical (γ : Matrix.GeneralLinearGroup (Fin 2) GF4) (z : GF4) :
    orth3Act γ (0, 0, z) = (0, 0, z) := by
  simp only [orth3Act, mul_zero, add_zero, zero_add]

lemma s16h_orth3Scal_apply (μ : GF4) (hμ : μ ≠ 0) (x y z : GF4) :
    orth3Scal μ hμ (Multiplicative.ofAdd (x, y, z)) =
      Multiplicative.ofAdd (μ * x, μ * y, μ * z) :=
  rfl

lemma s16h_orth3Scal_one_apply (hμ : (1 : GF4) ≠ 0) (w : GF4 × GF4 × GF4) :
    orth3Scal 1 hμ (Multiplicative.ofAdd w) = Multiplicative.ofAdd w := by
  obtain ⟨x, y, z⟩ := w
  rw [s16h_orth3Scal_apply]
  simp

lemma s16h_orth3Phi_apply (x y z : GF4) :
    orth3Phi (Multiplicative.ofAdd (x, y, z)) =
      Multiplicative.ofAdd (x ^ 2, y ^ 2, z ^ 2) :=
  rfl

lemma s16h_orth3Phi_radical (z : GF4) :
    orth3Phi (Multiplicative.ofAdd (0, 0, z)) =
      Multiplicative.ofAdd (0, 0, z ^ 2) := by
  rw [s16h_orth3Phi_apply]
  simp

lemma s16h_orth3Scal_act_radical (μ : GF4) (hμ : μ ≠ 0)
    (γ : Matrix.GeneralLinearGroup (Fin 2) GF4) (z : GF4) :
    orth3Scal μ hμ (Multiplicative.ofAdd
        (orth3Act γ (Multiplicative.toAdd (Multiplicative.ofAdd (0, 0, z))))) =
      Multiplicative.ofAdd (0, 0, μ * z) := by
  simp only [toAdd_ofAdd, s16h_orth3Act_radical, s16h_orth3Scal_apply,
    mul_zero]

lemma s16h_orth3Scal_act_phi_radical (μ : GF4) (hμ : μ ≠ 0)
    (γ : Matrix.GeneralLinearGroup (Fin 2) GF4) (z : GF4) :
    orth3Scal μ hμ (Multiplicative.ofAdd
        (orth3Act γ (Multiplicative.toAdd
          (orth3Phi (Multiplicative.ofAdd (0, 0, z)))))) =
      Multiplicative.ofAdd (0, 0, μ * z ^ 2) := by
  simp only [s16h_orth3Phi_radical, toAdd_ofAdd, s16h_orth3Act_radical,
    s16h_orth3Scal_apply, mul_zero]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
