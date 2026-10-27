module

import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.Foundations.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartOne.KLC

open Subgroup

theorem two_le_pRank_of_two_commuting {P : Type*} [Group P] [Finite P] {p : ℕ} (hp : p.Prime)
    {e₁ e₂ : P} (hc : Commute e₁ e₂) (h₁ : e₁ ^ p = 1) (h₂ : e₂ ^ p = 1)
    (hi : ∀ i j : ℤ, e₁ ^ i * e₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) :
    2 ≤ CFSG.pRank p P := CFSG.two_le_pRank_of_commute_independent hp hc h₁ h₂ hi

theorem pRank_congr_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (e : X ≃* Y)
    {p : ℕ} (_hp : 1 < p) : CFSG.pRank p X = CFSG.pRank p Y := CFSG.pRank_congr_of_mulEquiv e p

end CFSG.RankThree.PartOne.KLC
