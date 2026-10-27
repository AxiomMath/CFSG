module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoAltSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoLn
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoOmSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoOmEight

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_s1_case2_of_162_2 (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (h : Case162_2 D V₀ V hV L) :
    Case168_1 D V₀ V hV L ∨ Case168_2Star D V₀ V hV L := by
  obtain ⟨hs, hcase⟩ := h
  rcases hcase with ⟨n, hn5, hn11, hA, hsum⟩ | ⟨m, hm3, hm5, hLm, hsum⟩ | ⟨hSp, hsum⟩ |
    ⟨hOm, hsum⟩ | ⟨hOm, hsum⟩
  · by_cases hn6 : n = 6
    · subst hn6
      exact s16e_s1_two_alt_six D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hA hsum
    · exact Or.inr (s16e_s1_two_alt D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hn5 hn11 hn6
        hA hsum)
  · exact Or.inr (s16e_s1_two_ln D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hm3 hm5 hLm hsum)
  · exact Or.inr (s16e_s1_two_sp D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hSp hsum)
  · exact Or.inr (s16e_s1_two_om_six D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hOm hsum)
  · exact Or.inr (s16e_s1_two_om_eight D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hOm hsum)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
