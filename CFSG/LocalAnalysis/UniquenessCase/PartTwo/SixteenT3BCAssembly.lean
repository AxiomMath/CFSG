module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3GapInspBC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1Tr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3BCOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3BCSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3BCEleven
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Twelve

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16GapInspBC_of_three (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h111 : W3Thm111 G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h10 : R16_10_1 D) (h11 : R16_11 D) : S16GapInspBC D := by
  intro V L hV hc hnc hcomm hΓ
  have hC : ¬ centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M :=
    (sixteen_seven2_twelve D h10 h11 ⊥ V L hV hc).1
  rcases hc.concl168 with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11
  · exact s16t_insp_of_case168_1 D hx h61 h111 hSg h1219 hC hc c1
  · have hv : v1Sub D.M ⊥ V hV L = ⊥ :=
      s16e_v1Sub_eq_bot D hSg h61 hc.setting rfl (Or.inl c2) hC
    exact s16c13bc_case168_2 D hc hcomm ((s16e_case168_2Star_iff D ⊥ V L hV hv).1 c2)
  · exact (hnc (s16c13bc_oddNcCore_of_case168_3 D hV hc c3)).elim
  · exact (hnc (s16c13bc_oddNcCore_of_case168_4 D hV hc c4)).elim
  · have hv : v1Sub D.M ⊥ V hV L = ⊥ :=
      s16e_v1Sub_eq_bot D hSg h61 hc.setting rfl (Or.inr c5) hC
    exact s16c13bc_case168_5 D hc hcomm ((s16e_case168_5Star_iff D ⊥ V L hV hv).1 c5)
  · exact s16c13bc_case168_6 D hc hcomm c6
  · exact s16t_insp_of_case168_7 D hSg hc.setting.hyp16.hyp125 c7 hcomm
  · exact (hnc (s16c167_oddNcCore_of_case168_8 D hV c8)).elim
  · exact s16c13bc_case168_9 D hc hcomm (hΓ c9) c9
  · exact (hnc (s16c167_oddNcCore_of_case168_10 D hV c10)).elim
  · exact (hnc (s16t_oddNcCore_of_case168_11 D hV hc c11)).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
