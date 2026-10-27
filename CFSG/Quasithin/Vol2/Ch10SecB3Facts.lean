module

public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def FactCommNatSL : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H A : Subgroup (MulAut V)) (Z : Subgroup V)
    (d a p : ℕ), 2 ≤ d → BinaryNaturalSL H ⊤ Z d a → p.Prime → p ≠ 2 → ¬ p ∣ Nat.card H →
    IsPGroup p A → (∀ x ∈ A, ∀ h ∈ H, x * h = h * x) → (∀ x ∈ A, ∀ z ∈ Z, x z ∈ Z) →
    ∀ x ∈ A, ∀ v : V, x v * v⁻¹ ∈ Z

@[expose] def FactCommAlt5 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H A : Subgroup (MulAut V)) (Z : Subgroup V) (p : ℕ),
    AlternatingNatural H ⊤ Z 5 → p.Prime → p ≠ 2 → ¬ p ∣ Nat.card H → IsPGroup p A →
    (∀ x ∈ A, ∀ h ∈ H, x * h = h * x) → (∀ x ∈ A, ∀ z ∈ Z, x z ∈ Z) →
    ∀ x ∈ A, ∀ v : V, x v * v⁻¹ ∈ Z

@[expose] def FactCommOrth : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H A : Subgroup (MulAut V)) (Z : Subgroup V) (a p : ℕ),
    BinaryOrthogonalFour H ⊤ Z a → p.Prime → p ≠ 2 → ¬ p ∣ Nat.card H → IsPGroup p A →
    (∀ x ∈ A, ∀ h ∈ H, x * h = h * x) → (∀ x ∈ A, ∀ z ∈ Z, x z ∈ Z) →
    ∀ x ∈ A, ∀ v : V, x v * v⁻¹ ∈ Z

@[expose] def FactCommSz : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H A : Subgroup (MulAut V)) (Z : Subgroup V) (f p : ℕ),
    BinaryNaturalSz H ⊤ Z f → p.Prime → p ≠ 2 → ¬ p ∣ Nat.card H → IsPGroup p A →
    (∀ x ∈ A, ∀ h ∈ H, x * h = h * x) → (∀ x ∈ A, ∀ z ∈ Z, x z ∈ Z) →
    ∀ x ∈ A, ∀ v : V, x v * v⁻¹ ∈ Z

@[expose] def FactCommL3Pair : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)) (W₁ W₂ : Subgroup V),
    W₁ ⊔ W₂ = ⊤ → W₁ ⊓ W₂ = ⊥ → BinaryNaturalSL H W₁ ⊥ 3 1 → BinaryNaturalSL H W₂ ⊥ 3 1 →
    ¬ SecIsoL H W₁ ⊥ W₂ ⊥ → ∀ x : MulAut V, (∀ h ∈ H, x * h = h * x) → x = 1

@[expose] def FactCommGL4 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H A : Subgroup (MulAut V)) (U : Subgroup V) (p : ℕ),
    DirectSumOfCopies H U ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 4 → p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card H → IsPGroup p A → (∀ x ∈ A, ∀ h ∈ H, x * h = h * x) →
    (∀ x ∈ A, ∀ u ∈ U, x u ∈ U) → (∃ u ∈ U, u ≠ 1 ∧ ∀ x ∈ A, x u = u) →
    ∀ x ∈ A, ∀ u ∈ U, x u = u

end CFSG.Quasithin.Vol2.Ch10.SecB
