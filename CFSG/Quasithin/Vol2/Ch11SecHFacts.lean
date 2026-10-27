module

public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def FactTransvInSL3 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥(StatedSL 3 F) →* ↥H),
      (FFModel.nat (StatedSL 3 F)).RealizesVia H ⊤ ⊥ π →
      ∀ y : MulAut W, y ∈ Subgroup.normalizer (H : Set (MulAut W)) → y * y = 1 →
        Nat.card W ≤ 2 ^ n * Nat.card {w : W // y w = w} → y ∈ H

@[expose] def FactAxisGroupSp4 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥(StatedSp 2 F) →* ↥H),
      (FFModel.nat (StatedSp 2 F)).RealizesVia H ⊤ ⊥ π →
      ∀ (E : Subgroup (MulAut W)) (U : Subgroup W),
        E ≤ Subgroup.normalizer (H : Set (MulAut W)) → (∀ x ∈ E, x * x = 1) →
        (∀ x ∈ E, ∀ u ∈ U, x u = u) → Nat.card W ≤ 2 ^ n * Nat.card U → Nat.card E ≤ 2 ^ n

@[expose] def FactSL2NatBorel : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (U : Subgroup W) (π : ↥(StatedSL 2 F) →* ↥H),
      (FFModel.nat (StatedSL 2 F)).RealizesVia H U ⊥ π →
      ∀ S : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf S H →
      ∀ y ∈ H, y ∈ Subgroup.normalizer (S : Set (MulAut W)) → Odd (orderOf y) →
        ∃ μ : W →* W, (∀ u ∈ U, μ u ∈ U) ∧ (∀ h ∈ H, ∀ u ∈ U, μ (h u) = h (μ u)) ∧
          Nat.card {u : W // u ∈ U ∧ ∀ s ∈ S, s u = u} = 2 ^ n ∧
          (∀ u ∈ U, (∀ s ∈ S, s u = u) → μ (y u) = u) ∧
          (∀ u ∈ U, ∀ s ∈ S, s (y u * (μ u)⁻¹) = y u * (μ u)⁻¹) ∧
          ((∀ u ∈ U, (∀ s ∈ S, s u = u) → y u = u) → ∀ u ∈ U, y u = u)

@[expose] def FactSL2TwoSylow : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    ∀ S₁ S₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F),
      QuasithinUnique.IsSylowTwoOf S₁ ⊤ → QuasithinUnique.IsSylowTwoOf S₂ ⊤ → S₁ ≠ S₂ →
        S₁ ⊔ S₂ = ⊤

@[expose] def FactSL2BorelFPF : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    ∀ S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F), QuasithinUnique.IsSylowTwoOf S ⊤ →
    ∀ y ∈ Subgroup.normalizer (S : Set (Matrix.SpecialLinearGroup (Fin 2) F)),
      Odd (orderOf y) → y ≠ 1 → ∀ s ∈ S, y * s * y⁻¹ = s → s = 1

end CFSG.Quasithin.Vol2.Ch11.SecH
