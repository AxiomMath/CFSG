module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCASix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCATwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3GapInspA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1Tr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16GapInspA_holds (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h4 : 3 < CFSG.Open.evenRank G) (h12 : R16_12 D) : S16GapInspA D := by
  intro hSg V L hV hc hn _ hr
  obtain ⟨hC, -⟩ := h12 ⊥ V L hV hc
  rcases hc.concl168 with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11
  · exact (s16c1610_false_of_case1_four D hx h61 h127 hc h4 c1).elim
  · have hv : v1Sub D.M ⊥ V hV L = ⊥ :=
      s16e_v1Sub_eq_bot D hSg h61 hc.setting rfl (Or.inl c2) hC
    exact s16c13bcA_case168_2 D hx h61 h127 h4 hc (fun hs => hn (Or.inl hs))
      ((s16e_case168_2Star_iff D ⊥ V L hV hv).mp c2)
  · exact (hn (Or.inr (Or.inr (Or.inl c3)))).elim
  · obtain ⟨r, hr1, hw⟩ := (case168_4_iff_with D ⊥ V hV L).mp c4
    rcases (by omega : r = 2 ∨ r = 3 ∨ 3 < r) with rfl | rfl | hr3
    · exact s16c13bcA_case168_4_two D hx h61 h127 h4 hc hw
    · exact (hn (Or.inr (Or.inl hw))).elim
    · exact (hr ⟨r, hr3, hw⟩).elim
  · have hv : v1Sub D.M ⊥ V hV L = ⊥ :=
      s16e_v1Sub_eq_bot D hSg h61 hc.setting rfl (Or.inr c5) hC
    exact s16c13bcA_case168_5 D hc ((s16e_case168_5Star_iff D ⊥ V L hV hv).mp c5)
  · exact s16c13bcA_case168_6 D hc c6
  · exfalso
    have h7σ : 7 ∈ D.sig := by
      obtain ⟨-, -, -, h7⟩ := c7
      rw [h7]
      exact Set.mem_singleton 7
    have h3 := s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 hc.setting.hyp16 hV h4 h7σ
    have h2 := s16n9b_case7_pRank_lt D hV c7
    omega
  · exact (hn (Or.inr (Or.inr (Or.inr (Or.inl c8))))).elim
  · exact (hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c9)))))).elim
  · exact (hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c10))))))).elim
  · exact (hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr c11))))))).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
