module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeSCFourDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGTwE6SCFourNotTwoLocalOdd (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Odd (Nat.card ψ.ker) →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      Nat.card A = 3 ^ 4 → GGTorusSelfCent 3 A →
      ¬ ∃ V : Subgroup R, V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ a ∈ A, ∀ l : L', ψ l ∈ V → ψ (a l) ∈ V

@[expose] def GGTwE6ThreeSCFourNotTwoLocalOddInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 →
    3 ∣ 2 ^ n + 1 →
      GGTwE6SCFourNotTwoLocalOdd (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

end CFSG.StandardType
