module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly

@[expose] def GGTwE6CubeNodeInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → 3 ∣ 2 ^ n + 1 →
    ∀ Y : Subgroup (MulAut (TwE6Delta.RecipeR K n)), IsElemAbelian 3 Y →
      (Y : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n →
      Nat.card Y = 3 ^ 6 →
      ∀ x ∈ Y, x ≠ 1 → IsComponentOf (LargeEvenLayer (ggFix x)) (ggFix x) →
        (∀ y ∈ Y, (∀ j ∈ LargeEvenLayer (ggFix x), y j = j) ↔ y ∈ Subgroup.zpowers x) →
        ∀ E : Subgroup (TwE6Delta.RecipeR K n), IsElemAbelian 3 E → E ≤ ggFix x →
          Nat.card E ≤ 3 * Nat.card (E ⊓ LargeEvenLayer (ggFix x) : Subgroup _)

end CFSG.StandardType.SmallExc

end
