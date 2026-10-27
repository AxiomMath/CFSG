module

public import CFSG.RankThree.PartOne.S12.InputsSec15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

@[expose] def CoverActsTriviallyOnSmall (p : ℕ) (L : Type*) [Group L] : Prop :=
  ∀ (J : Type) [Group J] [Finite J], Group.IsPerfect J → ∀ φ : J →* L, Function.Surjective φ →
    Nat.Coprime (Nat.card φ.ker) (2 * p) → IsSolvable φ.ker →
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ≠ p →
    ∀ (V : Type) [Group V] [Finite V], (∀ a b : V, a * b = b * a) → (∀ v : V, v ^ ℓ = 1) →
      Nat.card V ≤ ℓ ^ 4 → ∀ ρ : J →* MulAut V, ρ = 1

@[expose] def CentralizerHasPElementOutside (p : ℕ) {X : Type*} [Group X] (N : Subgroup X) :
    Prop :=
  ∀ x y : X, x ∈ N → y ∈ N → x ≠ 1 → IsPGroup p (Subgroup.zpowers x) → (orderOf y).Prime →
    orderOf y ≠ 2 → orderOf y ≠ p → x * y = y * x →
    ∃ c ∈ CFSG.generalizedFitting X, c * y = y * c ∧ IsPGroup p (Subgroup.zpowers c) ∧ c ∉ N

@[expose] def CoverHasLargeTwoLocal (L : Type*) [Group L] : Prop :=
  ∀ (J : Type) [Group J] [Finite J], Group.IsPerfect J → ∀ φ : J →* L, Function.Surjective φ →
    φ.ker ≤ Subgroup.center J → Odd (Nat.card φ.ker) →
    ∃ U : Subgroup J, U ≠ ⊥ ∧ IsPGroup 2 U ∧
      4 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (U : Set J))

@[expose] def StronglyEmbeddedFive : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → CFSG.pPrimeCore p X = ⊥ →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) → ∀ N : Subgroup X, IsStronglyPEmbedded p N →
        CoverActsTriviallyOnSmall p ↥(CFSG.generalizedFitting X) ∧
          ((CFSG.pPrimeCore p ↥N = ⊥ ∧ CentralizerHasPElementOutside p N) ∨
            CoverHasLargeTwoLocal ↥(CFSG.generalizedFitting X))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
