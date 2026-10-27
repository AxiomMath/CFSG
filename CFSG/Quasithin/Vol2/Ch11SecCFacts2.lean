module

public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def FactAStarSylow : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (n : ℕ), 2 ≤ n → ∀ (Hs Ks : Subgroup (MulAut W)), Ks ≤ Hs →
      Hs ≤ Subgroup.normalizer (Ks : Set (MulAut W)) →
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        Nonempty (↥Ks ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
      (∀ h ∈ Hs, ∃ e : ℕ, h ^ 2 ^ e ∈ Ks) →
      CFSG.pCore 2 ↥Hs = ⊥ →
      ∀ A ∈ E3.aSet n Hs, QuasithinUnique.IsSylowTwoOf A Ks

@[expose] def FactSL2NatFPF : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    ∀ (W : Type) [CommGroup W] (H : Subgroup (MulAut W)) (U Z : Subgroup W)
      (π : ↥(StatedSL 2 F) →* ↥H), (FFModel.nat (StatedSL 2 F)).RealizesVia H U Z π →
      ∀ h ∈ H, Odd (orderOf h) → h ≠ 1 → ∀ u ∈ U, h u * u⁻¹ ∈ Z → u ∈ Z

@[expose] def FactTorusLineSL3 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSL 3 F) →* ↥H),
      (FFModel.nat (StatedSL 3 F)).RealizesVia H ⊤ Z π →
      ∀ S : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf S H →
        Nat.card {w : W // ∀ s ∈ S, s w * w⁻¹ ∈ Z} = 2 ^ n * Nat.card Z ∧
        ∀ y ∈ H, y ∈ Subgroup.normalizer (S : Set (MulAut W)) →
          (∀ w : W, (∀ s ∈ S, s w * w⁻¹ ∈ Z) → y w * w⁻¹ ∈ Z) ∨
          (∀ w : W, (∀ s ∈ S, s w * w⁻¹ ∈ Z) → y w * w⁻¹ ∈ Z → w ∈ Z)

@[expose] def FactTorusLineSp4 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 F) →* ↥H),
      (FFModel.nat (StatedSp 2 F)).RealizesVia H ⊤ Z π →
      ∀ S : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf S H →
        Nat.card {w : W // ∀ s ∈ S, s w * w⁻¹ ∈ Z} = 2 ^ n * Nat.card Z ∧
        ∀ y ∈ H, y ∈ Subgroup.normalizer (S : Set (MulAut W)) →
          (∀ w : W, (∀ s ∈ S, s w * w⁻¹ ∈ Z) → y w * w⁻¹ ∈ Z) ∨
          (∀ w : W, (∀ s ∈ S, s w * w⁻¹ ∈ Z) → y w * w⁻¹ ∈ Z → w ∈ Z)

end CFSG.Quasithin.Vol2.Ch11.SecC
