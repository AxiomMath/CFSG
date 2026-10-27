module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G44Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G44Swap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem r16_44_of (D : Data G) (h22 : R1622 D) (h41 : R16_41 D) (h42 : R16_42 D)
    (hkitB : OmegaKitB) (hkitD : OmegaKitD) : R16_44 D := by
  intro V₀ V L hV hS hc
  refine Set.Subset.antisymm ?_ ?_
  · rintro X ⟨g, rfl, hg⟩
    refine ⟨g, rfl, hg, s16c1G44_oneFirst h22 h41 h42 hkitB hkitD hS hc hg, ?_⟩
    exact (s16c1G44_oneDual_iff D.M V₀ V g).2
      (s16c1G44_oneFirst h22 h41 h42 hkitB hkitD hS hc ((s16c1G44_inCalO_inv 1 D.M V₀ V g).1 hg))
  · rintro X ⟨g, rfl, hg⟩
    exact ⟨g, rfl, hg.1⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
