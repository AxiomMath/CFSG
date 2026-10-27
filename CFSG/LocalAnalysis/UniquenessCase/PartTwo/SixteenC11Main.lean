module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Excl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Normal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11R1610Two
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Disp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10MainFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1Tr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.W3Lem45Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Certified


theorem r16_11_holds_of_four (hH1 : H1SpSixNatural) (D : Data G) (hin : In10 D)
    (h1217 : R1217 D) (h153 : R15_3Small D) (h4 : 3 < CFSG.Open.evenRank G) (h164 : R16_4 D)
    (hcase2 : In10 D → R16_10_2 D → 3 < CFSG.Open.evenRank G →
      ∀ {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}, Counterex16 D V₀ V L hV →
        Out10 D V₀ V hV → Case168_2 D V₀ V hV L →
          normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M) : R16_11 D := by
  have hout := out10_holds_of_four D hin h1217 h153 h4 h164
  have h1610 : R16_10_2 D :=
    r16_10_2_of_out10 D hin.hSg hin.h1219 hin.hx hin.h61 hin.h127 hin.h1114
      (w3Lem45_2_holds G) hout
  intro V₀ V L hV hc
  have hres : ¬ v1Sub D.M V₀ V hV L = V₀ →
      (Case168_2Star D V₀ V hV L ∨ Case168_5Star D V₀ V hV L) →
        normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
    intro hV1 h25
    have h0 : V₀ = ⊥ := by
      by_contra h0
      exact hV1 (v1Sub_of_ne_bot D.M V₀ V hV L h0)
    subst h0
    exact s16c11_normalizer_le_of_v1 hH1 D hin h1217 h1610 h4 h164 hc (hout ⊥ V L hV hc) h25 hV1
  rcases hc.concl168 with h1 | h2 | h3 | h4' | h5 | h6 | h7 | h8 | h9 | h10 | h11
  · exact (s16c1610_false_of_case1_four D hin.hx hin.h61 hin.h127 hc h4 h1).elim
  · by_cases hV1 : v1Sub D.M V₀ V hV L = V₀
    · exact hcase2 hin h1610 h4 hc (hout V₀ V L hV hc)
        ((s16e_case168_2Star_iff D V₀ V L hV hV1).1 h2)
    · exact hres hV1 (Or.inl h2)
  · exact s16c11_normalizer_le_of_case3 D hin.h61 h1610 hin.h169 hc h3
  · exact s16c11_normalizer_le_of_case4 D hin.h61 h1610 hin.h169 hc h4'
  · by_cases hV1 : v1Sub D.M V₀ V hV L = V₀
    · exact s16c11_normalizer_le_of_case5 D hin h1217 h1610 hc (hout V₀ V L hV hc)
        ((s16e_case168_5Star_iff D V₀ V L hV hV1).1 h5)
    · exact hres hV1 (Or.inr h5)
  · exact (s16c11_excl_case6 D hin.hx h4 h164 hc h6).elim
  · exact (s16c11_excl_case7 D hin.hx hin.h61 hin.h127 h4 hc h7).elim
  · exact (s16c11_excl_case8 D hin.hx hin.h61 hin.h127 h4 hc h8).elim
  · exact (s16c11_excl_case9 D hin.hx h4 h164 hc h9).elim
  · exact (s16c11_excl_case10 D hin.hx h4 h164 hc h10).elim
  · exact (s16c1610_false_of_case11_four D hin.hx hin.h61 hin.h127 hc h4 h11).elim

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
