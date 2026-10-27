module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67Fin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Rank
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r16_67aGap_of_four (D : Data G) (hext : DataExt D) (h127 : R127 D)
    (h4 : 3 < CFSG.Open.evenRank G) : R16_67aGap D := by
  intro _ _ h61 h1217 _ _ V₀ V L hV hS hsit
  exfalso
  have h3 := c23_evenRank_eq_three D hext (uc22p22q_r115_of D hext h61) h127 h1217 hS
    (Or.inr hsit.1)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
