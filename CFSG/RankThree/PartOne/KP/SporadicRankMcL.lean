module

public import CFSG.RankThree.PartOne.KP.SporadicDefs
public import CFSG.Sporadic.Schreier.PairMcLPairs

public section

namespace CFSG.RankThree.PartOne

open CFSG
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem sporadicCoprimeRank_McL : SporadicCoprimeRank .McL := by
  intro T _ _ ⟨e⟩ p hp hp5 hpT
  have hcardT : Nat.card T = 898128000 := by
    rw [Nat.card_congr e.toEquiv]
    exact Sporadic.McL.card_McL
  have h5 : p ≠ 5 := by
    rintro rfl
    exact hpT (by rw [hcardT]; norm_num)
  have h7 : p ≠ 7 := by
    rintro rfl
    exact hpT (by rw [hcardT]; norm_num)
  have hp11 : 11 ≤ p := by
    by_contra hlt
    have : p < 11 := by omega
    interval_cases p <;> omega
  refine ElementaryRankAtMostOne.of_outer_card_lt hp hpT ?_
  have hout : Nat.card (Outer T) ≤ 54 := by
    rw [card_outer_eq_of_mulEquiv e]
    exact Sporadic.Schreier.AT_McL_Schreier.1
  have : 121 ≤ p ^ 2 := by nlinarith
  omega

end CFSG.RankThree.PartOne
