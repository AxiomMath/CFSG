module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelNB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.GH74.KGroups Subgroup

theorem s16h_orth3_normalizer_form {n : MulAut Orth3}
    (hn : n ∈ Subgroup.normalizer (orth3L : Set (MulAut Orth3))) :
    (∃ (μ : GF4) (hμ : μ ≠ 0) (γ : ↥(StatedSL 2 GF4)), ∀ v : Orth3,
      n v = orth3Scal μ hμ (Multiplicative.ofAdd
        (orth3Act (γ : Matrix.GeneralLinearGroup (Fin 2) GF4) (Multiplicative.toAdd v)))) ∨
    (∃ (μ : GF4) (hμ : μ ≠ 0) (γ : ↥(StatedSL 2 GF4)), ∀ v : Orth3,
      n v = orth3Scal μ hμ (Multiplicative.ofAdd
        (orth3Act (γ : Matrix.GeneralLinearGroup (Fin 2) GF4)
          (Multiplicative.toAdd (orth3Phi v))))) := by
  rcases s16h_orth3_normalizer_lift hn with ⟨μ, hμ, γ, heq⟩ | ⟨μ, hμ, γ, heq⟩
  · left
    refine ⟨μ, hμ, γ, fun v => ?_⟩
    rw [heq, MulAut.mul_apply, s16h_orth3Aut_eq_orth3Act]
  · right
    refine ⟨μ, hμ, γ, fun v => ?_⟩
    rw [heq, MulAut.mul_apply, MulAut.mul_apply, s16h_orth3Aut_eq_orth3Act]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
