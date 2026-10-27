module

public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E2

@[expose] def E22TorusFacts : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n →
    (IsBenderOf n X ∨ IsPSL 3 2 n X ∨ IsPSp4 2 n X) →
    ∀ S : Subgroup X, IsSylowTwoOf S ⊤ →
      ∃ (Y Y' : Subgroup X) (w : X),
        Y ≤ Subgroup.normalizer (S : Set X) ∧ Y' ≤ Subgroup.normalizer (S : Set X) ∧
        Subgroup.normalizer (S : Set X) ≤ Y ⊔ Y' ⊔ S ∧
        IsCyclic ↥Y ∧ IsCyclic ↥Y' ∧ Nat.card Y = 2 ^ n - 1 ∧
        (∀ a ∈ Y, ∀ b ∈ Y', a * b = b * a) ∧
        w ∉ Subgroup.normalizer (S : Set X) ∧
        (∀ y ∈ Y, w * y * w⁻¹ = y⁻¹) ∧ ∀ y ∈ Y', w * y * w⁻¹ = y

@[expose] def E22TorusCover : Prop :=
  ∀ (X X' : Type) [Group X] [Group X'] [Finite X] (φ : X →* X') (n : ℕ),
    Function.Surjective φ → φ.ker ≤ Subgroup.center X → Odd (Nat.card φ.ker) → 2 ≤ n →
    (IsBenderOf n X' ∨ IsPSL 3 2 n X' ∨ IsPSp4 2 n X') →
    ∀ S : Subgroup X, IsSylowTwoOf S ⊤ →
      (∀ a ∈ Subgroup.normalizer (S : Set X), ∀ b ∈ Subgroup.normalizer (S : Set X),
          a * b * a⁻¹ * b⁻¹ ∈ S) ∧
      ∃ (Y : Subgroup X) (w : X), Y ≤ Subgroup.normalizer (S : Set X) ∧ IsCyclic ↥Y ∧
        Nat.card Y = 2 ^ n - 1 ∧ w ∉ Subgroup.normalizer (S : Set X) ∧
        ∀ y ∈ Y, w * y * w⁻¹ = y⁻¹

end E2

end CFSG.Quasithin
