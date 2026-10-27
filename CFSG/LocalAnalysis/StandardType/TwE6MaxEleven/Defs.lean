module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Order.Atoms
public import CFSG.Assembly.InCatalog
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.StandardType.TwE6MaxEleven

open CFSG.Assembly CFSG.Blueprint

structure LocalFacts (X : Type) [Group X] [Finite X] : Prop where
  card : Nat.card X = 2 ^ 36 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19
  simple : IsSimpleGroup X
  c11 : ∀ t : X, orderOf t = 11 → Nat.card (Subgroup.centralizer ({t} : Set X)) ∣ 2 * 3 * 11
  c17 : ∀ s : X, orderOf s = 17 → Nat.card (Subgroup.centralizer ({s} : Set X)) = 17
  rank3 : ∀ A : Subgroup X, (∀ a ∈ A, a ^ 3 = 1) → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
    Nat.card A ≤ 3 ^ 5
  elem11 : ∀ A : Subgroup X, (∀ a ∈ A, a ^ 3 = 1) → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
    Nat.card A = 3 ^ 5 → ∀ g ∈ Subgroup.normalizer (A : Set X), orderOf g ≠ 11
  levi : ∃ y₀ : X, orderOf y₀ = 3 ∧ ∃ L : Subgroup X,
    L ≤ Subgroup.centralizer ({y₀} : Set X) ∧ Nat.card L = 9196830720 ∧
    ∀ P : Subgroup X, P ≤ Subgroup.centralizer ({y₀} : Set X) → ⁅P, P⁆ = P → P ≤ L
  twoLocal : ∀ M : Subgroup X, IsCoatom M → ∀ U : Subgroup X, U ≠ ⊥ → IsPGroup 2 U →
    M ≤ Subgroup.normalizer (U : Set X) → ¬ 3 ^ 7 ∣ Nat.card M

@[expose] def ElevenSimpleCases : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], InCatalog S →
    (∃ a b : S, a * b ≠ b * a) →
    Nat.card S ∣ 2 ^ 36 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 →
    Nat.card S < 2 ^ 36 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 → 11 ∣ Nat.card S →
    ¬ 3 ^ 6 ∣ Nat.card S ∨ Nat.card S = 9196830720 ∨ Nat.card S = 25015379558400 ∨
      Nonempty (S ≃* NativeSporadic.Carrier .Suz) ∨ Nonempty (S ≃* NativeSporadic.Carrier .Fi22)

@[expose] def SporadicFacts : Prop :=
  Nat.card (NativeSporadic.Carrier .Fi22) = 64561751654400 ∧
    (∀ g : NativeSporadic.Carrier .Fi22, orderOf g ≠ 33) ∧
    (∀ g : NativeSporadic.Carrier .Suz, orderOf g ≠ 33) ∧
    ∀ σ : MulAut (NativeSporadic.Carrier .Suz), σ ^ 3 = 1 →
      ∃ n : NativeSporadic.Carrier .Suz, ∀ x, σ x = n * x * n⁻¹

end CFSG.StandardType.TwE6MaxEleven
