module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourDom
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGRootGenResQFourLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  2 ≤ lab.n ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1 ∧ (lab.tag = .twE6 ∨ lab.tag = .F4)

@[expose] def GGRootGenResLLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ p = 3 ∧ 2 ≤ lab.n ∧ 3 ∣ 2 ^ lab.n + 1

@[expose] def GGF4ThreePlusKGAvoid : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → 3 ∣ Nat.card K + 1 →
    GGTorusRootGenAvoidKG 3 4 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K)

@[expose] def GGTwE6ThreePlusKGAvoid : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = (2 ^ n) ^ 2 → 3 ∣ 2 ^ n + 1 →
    GGTorusRootGenAvoidKG 3 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

end CFSG.StandardType

end
