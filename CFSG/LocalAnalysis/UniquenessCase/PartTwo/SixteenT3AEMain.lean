module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3GapAEmpty
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAEThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3GapM
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AEBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AENine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Twelve

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16t_gapAEmpty_of_three (D : Data G) (h1217 : R1217 D) (h153 : R15_3Small D)
    (h10 : R16_10_1 D) (h11 : R16_11 D) : S16GapAEmpty D := by
  intro V L hV hc hcase
  have hm : 1 < mBar D.M ⊥ V hV := s16t_gapMGtOne_of_three D h1217 h153 V L hV hc
  rcases hcase with h3 | ⟨r, hr, h4⟩ | h8 | h9 | h10' | h11'
  · exact s16ae_calABar_eq_empty_of_case168_3 D hc hm h3
  · exact s16t_calABar_eq_empty_of_case168_4With D hc hm hr h4
  · exact s16t_calABar_eq_empty_of_case168_8 D h8 (by omega)
  · exact s16t_calABar_eq_empty_of_case168_9 D h1217 hc
      ((sixteen_seven2_twelve D h10 h11 ⊥ V L hV hc).2.2 h9) h9
  · exact s16t_calABar_eq_empty_of_case168_10 D h10' (by omega)
  · exact s16t_calABar_eq_empty_of_case168_11 D hc hm h11'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
