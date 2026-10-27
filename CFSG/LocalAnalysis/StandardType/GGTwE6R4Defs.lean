module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag

public section

namespace CFSG.StandardType

open CFSG.Open

@[expose] def GGTwE6ThreeNoRankSixInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 →
    3 ∣ 2 ^ n + 1 → ¬ 9 ∣ 2 ^ n + 1 →
      ∀ T : Subgroup (TwE6Delta.RecipeR K n), IsElemAbelian 3 T → Nat.card T ≠ 3 ^ 6

end CFSG.StandardType
