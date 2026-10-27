module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelNBA1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelNBA2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelNBB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.GH74.KGroups CFSG.Open CFSG.Quasithin CFSG.Quasithin.H
open scoped Matrix

private theorem s16h_orth3Scal_mem_normalizer (μ : GF4) (hμ : μ ≠ 0) :
    orth3Scal μ hμ ∈ Subgroup.normalizer (orth3L : Set (MulAut Orth3)) :=
  Subgroup.centralizer_le_normalizer (orth3L : Set (MulAut Orth3)) (by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [s16h_orth3L_eq_range] at hx
    obtain ⟨γ, rfl⟩ := hx
    exact (s16h_orth3Scal_comm μ hμ γ).symm)

private theorem s16h_orth3Aut_mem_orth3L (γ : ↥(StatedSL 2 GF4)) :
    s16h_orth3Aut γ ∈ orth3L := by
  rw [s16h_orth3L_eq_range]
  exact ⟨γ, rfl⟩

theorem s16h_orth3_normalizer_lift {n : MulAut Orth3}
    (hn : n ∈ Subgroup.normalizer (orth3L : Set (MulAut Orth3))) :
    (∃ (μ : GF4) (hμ : μ ≠ 0) (γ : ↥(StatedSL 2 GF4)),
      n = orth3Scal μ hμ * s16h_orth3Aut γ) ∨
    (∃ (μ : GF4) (hμ : μ ≠ 0) (γ : ↥(StatedSL 2 GF4)),
      n = orth3Scal μ hμ * s16h_orth3Aut γ * orth3Phi) := by
  rcases s16h_orth3_normalizer_quotient hn with ⟨μ, hμ, γ, h⟩ | ⟨μ, hμ, γ, h⟩
  · left
    exact ⟨μ, hμ, γ, s16h_orth3_normalizer_quotient_faithful hn
      (mul_mem (s16h_orth3Scal_mem_normalizer μ hμ)
        (Subgroup.le_normalizer (s16h_orth3Aut_mem_orth3L γ))) h⟩
  · right
    exact ⟨μ, hμ, γ, s16h_orth3_normalizer_quotient_faithful hn
      (mul_mem (mul_mem (s16h_orth3Scal_mem_normalizer μ hμ)
        (Subgroup.le_normalizer (s16h_orth3Aut_mem_orth3L γ)))
        s16h_orth3Phi_mem_normalizer) h⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
