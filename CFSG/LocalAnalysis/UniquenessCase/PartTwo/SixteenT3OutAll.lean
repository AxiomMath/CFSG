module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3OneOut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3Out4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3E9Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3TenThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3TenSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3ElevOut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Z7

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

section Certified


theorem s16t_out10_of_concl168_three (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    (h153 : R15_3Small D) (h119 : F11.R119 D) (h78 : R7_8At3 D)
    (h96 : UC9R96.R9_6At7 D) (h921 : R9_21Opp D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) : Out10 D V₀ V hV := by
  rcases hc.concl168 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
  · exact s16t_out10_of_case168_1_three D hin h1217 h153 hc h1
  · obtain ⟨hK, ⟨L₀, hdir, hshape⟩, hσ⟩ := h2
    rcases hshape with ⟨n, hn5, hn11, hS, -, hsum⟩ | ⟨m, hm3, hm5, hL₀, hL, hsum⟩ |
      ⟨hS, -, hsum⟩ | ⟨hO, hO', hsum⟩ | ⟨hO, hO', hsum⟩
    · exact s16c1610_out10_of_case2_sym D hin hc hK hσ hdir hn5 hn11 hS hsum
    · by_cases hcase : V₀ ≠ ⊥ ∧ m = 4
      · obtain ⟨hV₀, rfl⟩ := hcase
        exact (s16t_false_of_case2_l4_v0 D hin h119 h78 h96 h921 hc
          ⟨hK, ⟨L₀, hdir, hL₀, hL, hsum⟩, hσ⟩ hV₀).elim
      · exact s16c1610_out10_of_case2_ln D hin hc hK hσ hdir hm3 hm5
          (fun h1 h2 => absurd ⟨h1, h2⟩ hcase) hL₀ hL hsum
    · exact s16c1610_out10_of_case2_sp D hin hc hK hσ hdir hS hsum
    · exact s16c1610_out10_of_case2_ominus_six D hin hc hK hσ hdir hO hO' hsum
    · exact s16c1610_out10_of_case2_ominus_eight D hin hc hK hσ hdir hO hO' hsum
  · exact s16c1610_out10_of_case3 D hin hc h3
  · obtain ⟨p, r, hp, hr, h4'⟩ := h4
    exact s16t_out10_of_case168_4_three D hin h1217 h153 hc hp hr h4'
  · exact s16c1610_out10_of_case5 D hin hc h5
  · exact s16c1610_out10_of_case6 D hin hc h6
  · exact s16c1610_out10_of_case7 D hin hc h7
  · exact s16t_out10_of_case168_8_three D hin h1217 h153 hc h8
  · exact s16c1610_out10_of_case9 D hin hc h9
  · obtain ⟨p, hp, h10'⟩ := h10
    rcases hp with rfl | rfl
    · exact s16t_out10_of_case168_10_three D hin h1217 h153 hc h10'
    · exact s16t_out10_of_case168_10_seven D hin h1217 hc h10'
  · exact s16t_out10_of_case168_11_three D hin h1217 hc h11

theorem s16t_r16_10_1_of_three (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    (h153 : R15_3Small D) (h119 : F11.R119 D) (h78 : R7_8At3 D)
    (h96 : UC9R96.R9_6At7 D) (h921 : R9_21Opp D) : R16_10_1 D :=
  r16_10_1_of_out10 D hin.hSg hin.h1219 hin.hx hin.h61 hin.h127 hin.h1114 hin.h126
    (fun _ _ _ _ hc => s16t_out10_of_concl168_three D hin h1217 h153 h119 h78 h96 h921 hc)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
