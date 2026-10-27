module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelSylA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelN

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.GH74.KGroups CFSG.Open CFSG.Quasithin CFSG.Quasithin.H
open scoped Matrix

theorem s16h_orth3Q_normalizer {n : MulAut Orth3}
    (hn : n ∈ Subgroup.normalizer (orth3L : Set (MulAut Orth3))) {v : Orth3}
    (hv : s16h_orth3Q v = 0) : s16h_orth3Q (n v) = 0 := by
  rcases s16h_orth3_normalizer_form hn with ⟨μ, hμ, γ, heq⟩ | ⟨μ, hμ, γ, heq⟩
  · rw [heq, s16h_orth3Q_scal, s16h_orth3Q_act, hv, mul_zero]
  · rw [heq, s16h_orth3Q_scal, s16h_orth3Q_act, s16h_orth3Q_phi, hv]
    ring

theorem s16h_orth3Sing_normalizer_mem {n : MulAut Orth3}
    (hn : n ∈ Subgroup.normalizer (orth3L : Set (MulAut Orth3))) {v : Orth3}
    (hv : v ∈ s16h_orth3Sing) : n v ∈ s16h_orth3Sing := by
  rw [s16h_mem_orth3Sing] at hv ⊢
  refine ⟨?_, s16h_orth3Q_normalizer hn hv.2⟩
  intro h1
  exact hv.1 ((MulEquiv.map_eq_one_iff n).mp h1)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
