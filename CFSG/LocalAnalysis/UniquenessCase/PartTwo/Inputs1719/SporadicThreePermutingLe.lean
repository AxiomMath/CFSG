module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONanLocal17

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_SporadicThreePermutingLe (r : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y) (s : TauCeti.SporadicName),
    K.Normal →
    CFSG.Open.IsQuasisimple ↥K →
    Odd (Nat.card (Subgroup.center ↥K)) →
    IsSpor (↥K ⧸ Subgroup.center ↥K) s →
    Subgroup.centralizer (K : Set Y) = (Subgroup.center ↥K).map K.subtype →
    (∃ n : ℕ, K.index = 2 ^ n) →
    CFSG.Quasithin.IsSylowIn 2 S ⊤ →
    2 < CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) → CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ r →
    s ≠ .ONan →
      ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
        ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S

theorem k_SporadicThreePermutingLe_of (h : K_SporadicThreePermuting) (r : ℕ) :
    K_SporadicThreePermutingLe r := by
  intro Y _ _ K S s hKN hQ hOdd hs hC hIdx hSyl hm3 _ hON
  exact h Y K S s hKN hQ hOdd hs hC hIdx hSyl hm3 hON

theorem K_SporadicThreePermutingLe.mono {r r' : ℕ} (hr : r ≤ r')
    (h : K_SporadicThreePermutingLe r') : K_SporadicThreePermutingLe r := by
  intro Y _ _ K S s hKN hQ hOdd hs hC hIdx hSyl hm3 hle hON
  exact h Y K S s hKN hQ hOdd hs hC hIdx hSyl hm3 (hle.trans hr) hON

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
