module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelNBA1B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelNBA1C

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.GH74.KGroups CFSG.Open CFSG.Quasithin CFSG.Quasithin.H
open scoped Matrix

theorem s16h_orth3_normalizer_quotient {n : MulAut Orth3}
    (hn : n ∈ Subgroup.normalizer (orth3L : Set (MulAut Orth3))) :
    (∃ (μ : GF4) (hμ : μ ≠ 0) (γ : ↥(StatedSL 2 GF4)), ∀ v : Orth3,
      n v * ((orth3Scal μ hμ * s16h_orth3Aut γ) v)⁻¹ ∈ orth3Z) ∨
    (∃ (μ : GF4) (hμ : μ ≠ 0) (γ : ↥(StatedSL 2 GF4)), ∀ v : Orth3,
      n v * ((orth3Scal μ hμ * s16h_orth3Aut γ * orth3Phi) v)⁻¹ ∈ orth3Z) := by
  rcases s16h_sl2_normalizer_add_form (s16h_ind n hn) (s16h_ind_normalizes n hn) with
    h1 | h2
  · rcases h1 with ⟨μ, hμ, γ, hform⟩
    left
    refine ⟨μ, hμ, γ, fun v => ?_⟩
    apply s16h_mem_Z_of_qp_eq
    rw [← s16h_ind_qp n hn v, hform (s16h_qp v)]
    simp only [MulAut.mul_apply]
    rw [s16h_qp_orth3Scal, s16h_qp_orth3Aut]
  · rcases h2 with ⟨μ, hμ, γ, hform⟩
    right
    refine ⟨μ, hμ, γ, fun v => ?_⟩
    apply s16h_mem_Z_of_qp_eq
    rw [← s16h_ind_qp n hn v, hform (s16h_qp v)]
    simp only [MulAut.mul_apply, MulAut.mul_apply]
    rw [s16h_qp_orth3Scal, s16h_qp_orth3Aut, s16h_qp_orth3Phi]
    rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
