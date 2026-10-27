module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open

@[expose] def KGen147 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsKGroup K → IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → CFSG.Open.pRank 3 (⊤ : Subgroup K) = 1 →
    ∀ B R : Subgroup K, Nat.card B = 3 → IsElemAbelian 7 R → Nat.card R = 49 →
      B ≤ normalizer (R : Set K) → R ⊓ centralizer (B : Set K) = ⊥ →
      ∀ H : Subgroup K, normalizer (B : Set K) ≤ H →
        (∀ Y : Subgroup K, R ≤ Y → IsPGroup 7 Y → normalizer (Y : Set K) ≤ H) → H = ⊤

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
