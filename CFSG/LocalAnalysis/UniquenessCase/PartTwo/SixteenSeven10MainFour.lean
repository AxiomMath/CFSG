module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case4Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Z7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10DirectOut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10MBarFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10OutFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10ElevenFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAETen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Certified


theorem out10_holds_of_four (D : Data G) (hin : In10 D) (h1217 : R1217 D) (h153 : R15_3Small D)
    (h4 : 3 < CFSG.Open.evenRank G) (h164 : R16_4 D) :
    ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D V₀ V L hV →
      Out10 D V₀ V hV := by
  intro V₀ V L hV hc
  rcases hc.concl168 with h1 | h2 | h3 | h4' | h5 | h6 | h7 | h8 | h9 | h10 | h11
  · exact (s16c1610_false_of_case1_four D hin.hx hin.h61 hin.h127 hc h4 h1).elim
  · exact s16c1610_out10_of_case2_four D hin h4 hc h2
  · exact s16c1610_out10_of_case3 D hin hc h3
  · obtain ⟨p, r, hp, hr, h4''⟩ := h4'
    by_cases h32 : p = 3 ∧ r = 2
    · obtain ⟨rfl, rfl⟩ := h32
      exact s16c1610_out10_of_case4_two_three D hin hc h4''
    · have hkm := s16c1610_k_lt_mBar_of_case4_four D hin h1217 h153 h4 hc hp hr h4''
      by_cases hr3 : r ≤ 3
      · exact s16c1610_out10_of_no_calOStar D hin.hx hin.h61 hin.h127 hin.h1114 hin.h162
          hc.setting.hyp16.hyp125 hkm
          (fun _ g => s16c1610_no_calOStar_of_case4_four D hin h4 hc hp hr hr3 h32 h4'' g)
      · exact s16c1610_out10_of_case4_big D hin hc hp (by omega) h4'' hkm
  · exact s16c1610_out10_of_case5 D hin hc h5
  · exact s16c1610_out10_of_case6 D hin hc h6
  · exact s16c1610_out10_of_case7 D hin hc h7
  · exact (r1613g_not_case168_8_of_four D hin.hx hin.h61 hin.h127 h4
      ⟨hc.setting, hc.ne_bot, hc.conc⟩ h8).elim
  · exact s16c1610_out10_of_case9 D hin hc h9
  · exact (s16ae_false_of_case168_10_of_r16_4 D hin.hx h164 h4 hc h10).elim
  · exact (s16c1610_false_of_case11_four D hin.hx hin.h61 hin.h127 hc h4 h11).elim

theorem r16_10_1_holds_of_four (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    (h153 : R15_3Small D) (h4 : 3 < CFSG.Open.evenRank G) (h164 : R16_4 D) : R16_10_1 D :=
  r16_10_1_of_out10 D hin.hSg hin.h1219 hin.hx hin.h61 hin.h127 hin.h1114 hin.h126
    (out10_holds_of_four D hin h1217 h153 h4 h164)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
