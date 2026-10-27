module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKStarA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKStarB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_star (h : S16kBase D V₀ V L hV) : S16kStar D V₀ V L hV := by
  by_cases h0 : V₀ = ⊥
  · exact s16k_star_of_eq_bot h h0
  · exact s16k_star_of_ne_bot h h0

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
