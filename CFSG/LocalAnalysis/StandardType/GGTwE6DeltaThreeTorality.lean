module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag

public section

namespace CFSG.StandardType.TwE6D3

open CFSG.Assembly

@[expose] def RankFiveInnInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 →
    9 ∣ 2 ^ n + 1 →
    ∀ X : Subgroup (MulAut (TwE6Delta.RecipeR K n)), IsElemAbelian 3 X →
      (X : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n → 3 ^ 5 ≤ Nat.card X →
      X ≤ (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range

end CFSG.StandardType.TwE6D3
