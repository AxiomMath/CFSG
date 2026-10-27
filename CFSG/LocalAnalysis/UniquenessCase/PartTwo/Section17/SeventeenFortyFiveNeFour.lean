module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveCaseThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem gap17_45_uniqueMaxFive_of_evenRank_le_three (D : Data G) (V₀ V : Subgroup G)
    (h3 : CFSG.Open.evenRank G ≤ 3) : Gap17_45_UniqueMaxFive D V₀ V := by
  intro L X p n l r C Dc Gamma x A₀ A B _ _ _ hc4
  exact absurd hc4.2.2.2.1 (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
