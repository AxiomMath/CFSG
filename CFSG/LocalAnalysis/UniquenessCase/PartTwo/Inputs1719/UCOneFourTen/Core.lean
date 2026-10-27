module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def UC1_4_10Core : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K L T Y : Subgroup X) (n : ℕ),
    CFSG.Open.IsKGroup X →
    (∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3) →
    CFSG.pCore 2 X = ⊥ →
    CFSG.Open.IsQuasisimple ↥K → K.Normal → centralizer (K : Set X) ≤ K → K ⊔ T = ⊤ →
    L ≤ K → ⁅L, L⁆ = L → IsSz (Bar2 L) n →
    Y ≠ ⊤ → CFSG.Open.IsSubnormal L Y →
    CFSG.ABGLocalTools.IsSylowOf 2 T (F08.CentOverO2 Y L) →
    normalizer (T : Set X) ≤ Y →
    (∀ A : Subgroup X, A ≤ L → (Nat.card A).Prime → Nat.card A ≠ 2 →
      normalizer (A : Set X) ≤ Y) →
    (∀ X₁ : Subgroup X, X₁ ≠ ⊤ → L ≤ X₁ → T ≤ X₁ → CFSG.Open.IsSubnormal L X₁) →
    False

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
