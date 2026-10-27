module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1F431Lift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem r16_43_1_of (D : Data G) (h22 : R1622 D) (h41 : R16_41 D) (h42 : R16_42 D)
    (hkitB : OmegaKitB) (hkitC : OmegaKitC) : R16_43_1 D := by
  intro V₀ V L hV hS hc i A g hy
  by_cases hg : g ∈ D.M
  · exact s16c1_431_barSub_le_of_mem hy hg hS
  by_contra hnot
  obtain ⟨Q, hQ, hQi⟩ := (h41 V₀ V L hV hS hc).1
  obtain ⟨a, haS, haA, w, hw⟩ := s16c1_431_outer hkitB hkitC hS hc hy hQ hQi hnot
  have h1 : ¬ V ≤ conjSubgroup D.M g :=
    s16c1_431_not_le_conj h22 h41 hS hc hy hg hQ hQi haS haA hw
  exact h1 (s16c1_431_finish hkitB hkitC h22 h42 hS hc hy hnot
    (s16c1_431_rank h22 h42 hS hc hy h1))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
