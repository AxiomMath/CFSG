module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRule
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeLift

public section

namespace CFSG.StandardType.SmallExc

@[expose] def GGTwE6EltNormSmallInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n p : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → p.Prime →
    p ∣ 2 ^ n + 1 → p ≠ 3 → GGStdSubTwoTorusEltNormSmall p 5 (TwE6Delta.RecipeR K n)

@[expose] def GGTwE6NormSmallThreeInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → 3 ∣ 2 ^ n + 1 →
    GGStdSubTwoTorusNormSmallR 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

@[expose] def GGTwE6DeltaSmallThreeInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → 3 ∣ 2 ^ n + 1 →
    GGStdSubTwoTorusDeltaSmall 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

end CFSG.StandardType.SmallExc

end
