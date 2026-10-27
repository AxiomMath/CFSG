module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCOdd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3GapInspBC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10ElevenFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1Tr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16GapInspBC_holds (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h4 : 3 < CFSG.Open.evenRank G) (hSg : UC6S846.SigmaStd D) (h12 : R16_12 D) :
    S16GapInspBC D := by
  intro V L hV hc hnc hcomm hΓ
  have hC : ¬ centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M := (h12 ⊥ V L hV hc).1
  rcases hc.concl168 with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11
  · exact (s16c1610_false_of_case1_four D hx h61 h127 hc h4 c1).elim
  · have hv : v1Sub D.M ⊥ V hV L = ⊥ :=
      s16e_v1Sub_eq_bot D hSg h61 hc.setting rfl (Or.inl c2) hC
    exact s16c13bc_case168_2 D hc hcomm ((s16e_case168_2Star_iff D ⊥ V L hV hv).1 c2)
  · exact (hnc (s16c13bc_oddNcCore_of_case168_3 D hV hc c3)).elim
  · exact (hnc (s16c13bc_oddNcCore_of_case168_4 D hV hc c4)).elim
  · have hv : v1Sub D.M ⊥ V hV L = ⊥ :=
      s16e_v1Sub_eq_bot D hSg h61 hc.setting rfl (Or.inr c5) hC
    exact s16c13bc_case168_5 D hc hcomm ((s16e_case168_5Star_iff D ⊥ V L hV hv).1 c5)
  · exact s16c13bc_case168_6 D hc hcomm c6
  · exfalso
    have h7σ : 7 ∈ D.sig := by
      rw [c7.2.2.2]
      exact Set.mem_singleton 7
    have h3 := s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 hc.setting.hyp16 hV h4 h7σ
    have h2 := s16n9b_case7_pRank_lt D hV c7
    omega
  · exact (hnc (s16c167_oddNcCore_of_case168_8 D hV c8)).elim
  · exact s16c13bc_case168_9 D hc hcomm (hΓ c9) c9
  · exact (hnc (s16c167_oddNcCore_of_case168_10 D hV c10)).elim
  · exact (s16c1610_false_of_case11_four D hx h61 h127 hc h4 c11).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
