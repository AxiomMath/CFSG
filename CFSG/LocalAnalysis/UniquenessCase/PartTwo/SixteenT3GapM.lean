module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gMParam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3GapM
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3Case1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3Case2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3Case3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16t_gapMGtOne_of_three (D : Data G) (h1217 : R1217 D) (h153 : R15_3Small D) :
    S16GapMGtOne D := by
  intro V L hV hc
  by_contra hlt
  have hMne : Mbar D.M ⊥ V hV ≠ ⊥ := by
    intro hbot
    apply hc.ne_bot
    exact le_bot_iff.mp
      ((barSub_mono ⊥ V hV hc.setting.hyp151.le).trans (le_of_eq hbot))
  have hne : mBar D.M ⊥ V hV ≠ 0 :=
    r1613g_mParam_ne_zero (s15_Infra_vtil_sq_eq_one ⊥ V hV) hMne
  have hm1 : mBar D.M ⊥ V hV = 1 := by omega
  rcases sixteen_one D h1217 h153 hc.setting.hyp151 hc.setting.hyp16.small hV hc.ne_bot hm1 with
    h1 | h2 | h3
  · exact s16t_false_of_case153_1 D h1217 hc h1
  · exact s16t_false_of_case153_2 D h1217 hc h2
  · exact s16t_false_of_case153_3 D h1217 hc h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
