module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwelveF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwelveG

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem fifteen_twelve (D : Data G) (h129 : R129_1 D) (h1217 : R1217 D) (hT7 : RT7 D) :
    R15_12 D := by
  intro V₀ V L h hL n hn2 hnγ hO
  have hV := h.hyp151.isElemAbelian
  obtain ⟨k, hk⟩ := exists_cond1512 hO
  have hs1 := fifteen_five D h129 h1217 h hV hL
  by_cases hI : n + 2 ≤ gamma15 D.M V₀ V hV L
  · obtain ⟨h3, h2⟩ := s15_Twelve_caseI D h1217 hT7 h hV hL hk hn2 hI hs1
    exact ⟨h3.le, h2⟩
  · have hγ : gamma15 D.M V₀ V hV L = n + 1 := by omega
    refine ⟨by omega, ?_⟩
    by_contra hs2
    rcases Nat.lt_or_ge (s15 D.M V₀ V hV L) 4 with h4 | h4
    · exact s15_Twelve_exc D h1217 h hV hL hk hn2 hγ (by omega)
    · exact s15_Twelve_bigS D h1217 h hV hL hk hn2 hγ h4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
