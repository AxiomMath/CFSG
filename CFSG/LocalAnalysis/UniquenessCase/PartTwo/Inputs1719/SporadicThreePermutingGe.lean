module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicThreePermutingLe

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_SporadicThreePermutingGe (r : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y) (s : TauCeti.SporadicName),
    K.Normal →
    CFSG.Open.IsQuasisimple ↥K →
    Odd (Nat.card (Subgroup.center ↥K)) →
    IsSpor (↥K ⧸ Subgroup.center ↥K) s →
    Subgroup.centralizer (K : Set Y) = (Subgroup.center ↥K).map K.subtype →
    (∃ n : ℕ, K.index = 2 ^ n) →
    CFSG.Quasithin.IsSylowIn 2 S ⊤ →
    2 < CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) → r ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) →
    s ≠ .ONan →
      ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
        ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S

theorem k_SporadicThreePermutingLe_of_le_ge {a : ℕ} (hle : K_SporadicThreePermutingLe a)
    (hge : K_SporadicThreePermutingGe (a + 1)) (r : ℕ) : K_SporadicThreePermutingLe r := by
  intro Y _ _ K S s hKN hQ hOdd hs hC hIdx hSyl hm3 _ hON
  by_cases ha : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ a
  · exact hle Y K S s hKN hQ hOdd hs hC hIdx hSyl hm3 ha hON
  · exact hge Y K S s hKN hQ hOdd hs hC hIdx hSyl hm3 (by omega) hON

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
