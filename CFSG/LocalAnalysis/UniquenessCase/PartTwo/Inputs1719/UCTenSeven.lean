module

public import CFSG.Open.Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup
open scoped commutatorElement

@[expose] def UC2_10_7w (G : Type) [Group G] [Finite G] : Prop :=
  CFSG.Open.IsKProper G →
  ∀ (s p : ℕ) (H M T B X Y : Subgroup G), Odd s → p.Prime → p ∣ 2 ^ s - 1 → H ≠ ⊤ →
    CFSG.ABGLocalTools.IsSylowOf 2 T H → B ≤ H → B ≤ normalizer (T : Set G) → Nat.card B = p →
    T ≤ M → B ≤ M → Y ≤ M →
    (∀ K : Subgroup G, K ≤ H → H ≤ normalizer (K : Set G) → K ≤ M → K ≤ Y) →
    (∀ g ∈ H, (∀ b ∈ B, g⁻¹ * b * g ∈ M) → g ∈ M) →
    Y ≤ X → X ≤ H → H ≤ normalizer (Y : Set G) → H ≤ normalizer (X : Set G) →
    ¬ X ≤ M → H ≤ (H ⊓ M) ⊔ X →
    (∀ W : Subgroup G, Y ≤ W → W ≤ X → H ≤ normalizer (W : Set G) → W = Y ∨ W = X) →
    ¬ ⁅X, X⁆ ≤ Y → ∀ c ∈ ⁅T, B⁆, ∀ x ∈ X, ⁅x, c⁆ ∈ Y

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
