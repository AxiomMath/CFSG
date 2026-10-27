module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open scoped commutatorElement Pointwise

@[expose] def UC2_10_7c : Prop :=
  ∀ (A : Type) [Group A] [Finite A], CFSG.Open.IsKGroup A →
    ∀ (s p : ℕ) (M T B X : Subgroup A), Odd s → p.Prime → p ∣ 2 ^ s - 1 →
      CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → B ≤ normalizer (T : Set A) → Nat.card B = p →
      T ≤ M → B ≤ M → (∀ g : A, (∀ b ∈ B, g⁻¹ * b * g ∈ M) → g ∈ M) →
      X.Normal → (∀ W : Subgroup A, W.Normal → W ≤ X → W = ⊥ ∨ W = X) →
      ¬ X ≤ M → M ⊔ X = ⊤ → ⁅X, X⁆ ≠ ⊥ →
      ⁅T, B⁆ ≤ centralizer (X : Set A)

@[expose] def UC2_10_7as : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A), L.Normal → IsSimpleGroup ↥L →
    (∃ a b : ↥L, a * b ≠ b * a) → centralizer (L : Set A) = ⊥ → CFSG.Open.IsCatalogGroup ↥L →
    ∀ (s p : ℕ) (T B M : Subgroup A), Odd s → p.Prime → p ∣ 2 ^ s - 1 →
      CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → B ≤ normalizer (T : Set A) → Nat.card B = p →
      L ⊔ T ⊔ B = ⊤ → T ≤ M → B ≤ M → (∀ g : A, (∀ b ∈ B, g⁻¹ * b * g ∈ M) → g ∈ M) →
      L ≤ M ∨ ⁅T, B⁆ = ⊥

@[expose] def UC2_10_7J1 : Prop :=
  ∀ (A : Type) [Group A] [Finite A], UC22.IsJ1 A →
    ∀ (T B M : Subgroup A), CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → B ≤ normalizer (T : Set A) →
      Nat.card B = 7 → T ≤ M → B ≤ M → (∀ g : A, (∀ b ∈ B, g⁻¹ * b * g ∈ M) → g ∈ M) → M = ⊤

@[expose] def KLieBorelAutPrimeRank2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : CFSG.Open.StatedLieTag) (m : ℕ),
    CFSG.Open.StatedLieAdmissible t m 2 1 → CFSG.Blueprint.LieModel X t m 2 1 →
    PartTwo.S17.CS17LieRank t m ≤ 2 → t ≠ .trialityD4 → t ≠ .Tits →
    ∀ U : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ → ∀ s r : ℕ, Odd s → r.Prime →
      7 ≤ r → r ∣ 2 ^ s - 1 → ∀ α : MulAut X, α ^ r = 1 → U.map α.toMonoidHom = U → α = 1

@[expose] def UC2_10_7Odd : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A), L.Normal → IsSimpleGroup ↥L →
    centralizer (L : Set A) = ⊥ → ∀ r : ℕ, r.Prime → r ≠ 2 → UC22.IsChev ↥L r →
    ∀ (s p : ℕ) (T B M : Subgroup A), Odd s → p.Prime → p ∣ 2 ^ s - 1 →
      CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → B ≤ normalizer (T : Set A) → Nat.card B = p →
      L ⊔ T ⊔ B = ⊤ → T ≤ M → B ≤ M → (∀ g : A, (∀ b ∈ B, g⁻¹ * b * g ∈ M) → g ∈ M) →
      L ≤ M ∨ ⁅T, B⁆ = ⊥

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
