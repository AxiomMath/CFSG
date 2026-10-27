module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCASix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3GapInspA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1Tr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3BCOne
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Twelve

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16GapInspA_of_three (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h111 : W3Thm111 G) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h1219 : D.sig = D.sig1) (h10 : R16_10_1 D) (h11 : R16_11 D)
    (hgap : S16GapA168FourThree D) : S16GapInspA D := by
  intro hSg V L hV hc hn hcomm hr
  have hC : ¬ centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M :=
    (sixteen_seven2_twelve D h10 h11 ⊥ V L hV hc).1
  rcases hc.concl168 with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11
  · exact s16t_insp_of_case168_1 D hx h61 h111 hSg h1219 hC hc c1
  · have hv : v1Sub D.M ⊥ V hV L = ⊥ :=
      s16e_v1Sub_eq_bot D hSg h61 hc.setting rfl (Or.inl c2) hC
    exact s16t_a_case168_2 D hx h61 h127 hc (fun hs => hn (Or.inl hs))
      ((s16e_case168_2Star_iff D ⊥ V L hV hv).mp c2)
  · exact (hn (Or.inr (Or.inr (Or.inl c3)))).elim
  · obtain ⟨r, hr1, hw⟩ := (case168_4_iff_with D ⊥ V hV L).mp c4
    rcases (by omega : r = 2 ∨ r = 3 ∨ 3 < r) with rfl | rfl | hr3
    · exact s16t_a_case168_4_two D hx h61 h127 hSg hgap hc hn hcomm hw
    · exact (hn (Or.inr (Or.inl hw))).elim
    · exact (hr ⟨r, hr3, hw⟩).elim
  · have hv : v1Sub D.M ⊥ V hV L = ⊥ :=
      s16e_v1Sub_eq_bot D hSg h61 hc.setting rfl (Or.inr c5) hC
    exact s16c13bcA_case168_5 D hc ((s16e_case168_5Star_iff D ⊥ V L hV hv).mp c5)
  · exact s16c13bcA_case168_6 D hc c6
  · exact s16t_a_insp_of_case168_7 D hx h61 h127 h1214 hSg hc.setting.hyp16.hyp125 c7
  · exact (hn (Or.inr (Or.inr (Or.inr (Or.inl c8))))).elim
  · exact (hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c9)))))).elim
  · exact (hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c10))))))).elim
  · exact (hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr c11))))))).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
