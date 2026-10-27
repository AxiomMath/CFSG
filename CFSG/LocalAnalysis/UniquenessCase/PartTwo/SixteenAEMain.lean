module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3GapAEmpty
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gGapM
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10ElevenFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAEThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAEFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAENine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAETen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16GapAEmpty_of_four (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1217 : R1217 D) (h153 : R15_3Small D) (h164 : R16_4 D)
    (h4 : 3 < CFSG.Open.evenRank G) : S16GapAEmpty D := by
  intro V L hV hc hcase
  have hm : 1 < mBar D.M ⊥ V hV := r1613g_gapMGtOne_of_four D hx h61 h127 h1217 h153 h4 V L hV hc
  rcases hcase with h3 | ⟨r, hr, h4'⟩ | h8 | h9 | h10 | h11
  · exact s16ae_calABar_eq_empty_of_case168_3 D hc hm h3
  · exact s16ae_calABar_eq_empty_of_case168_4With D hx h61 h127 h4 hc hm (by omega) h4'
  · exact (r1613g_not_case168_8_of_four D hx h61 h127 h4
      ⟨hc.setting, hc.ne_bot, hc.conc⟩ h8).elim
  · exact (s16ae_false_of_case168_9_of_r16_4 D hx h164 h4 hc h9).elim
  · exact (s16ae_false_of_case168_10_of_r16_4 D hx h164 h4 hc h10).elim
  · exact (s16c1610_false_of_case11_four D hx h61 h127 hc h4 h11).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
