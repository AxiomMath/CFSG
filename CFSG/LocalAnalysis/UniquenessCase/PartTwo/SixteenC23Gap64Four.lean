module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Gap64
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Rank
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23Gap64_of_four (D : Data G) (h4 : 3 < CFSG.Open.evenRank G) : C23Gap64 D := by
  intro _ hext h61 h127 _ h1217 _ _ _ V₀ V L hV hS hc _ _
  have h3 := c23_evenRank_eq_three D hext (uc22p22q_r115_of D hext h61) h127 h1217 hS (Or.inl hc)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
