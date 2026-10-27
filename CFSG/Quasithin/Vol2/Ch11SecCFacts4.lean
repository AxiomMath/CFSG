module

public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def FactTransvPointSL3 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥(StatedSL 3 F) →* ↥H),
      (FFModel.nat (StatedSL 3 F)).RealizesVia H ⊤ ⊥ π →
      ∀ S : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf S H →
      ∀ y : MulAut W, y ∈ Subgroup.normalizer (H : Set (MulAut W)) → y * y = 1 → y ≠ 1 →
        Nat.card W ≤ 2 ^ n * Nat.card {w : W // y w = w} →
        ∃ h ∈ H, ∀ w : W, (∃ w' : W, w = y w' * w'⁻¹) ↔ ∀ s ∈ S, s (h⁻¹ w) = h⁻¹ w

@[expose] def FactTransvPointSp4 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥(StatedSp 2 F) →* ↥H),
      (FFModel.nat (StatedSp 2 F)).RealizesVia H ⊤ ⊥ π →
      ∀ S : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf S H →
      ∀ y : MulAut W, y ∈ Subgroup.normalizer (H : Set (MulAut W)) → y * y = 1 → y ≠ 1 →
        Nat.card W ≤ 2 ^ n * Nat.card {w : W // y w = w} →
        ∃ h ∈ H, ∀ w : W, (∃ w' : W, w = y w' * w'⁻¹) ↔ ∀ s ∈ S, s (h⁻¹ w) = h⁻¹ w

end CFSG.Quasithin.Vol2.Ch11.SecC
