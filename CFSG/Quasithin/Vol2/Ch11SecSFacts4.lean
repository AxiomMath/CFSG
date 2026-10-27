module

public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch11SecAFactsFlag
public import CFSG.Quasithin.Vol2.Ch11SecSBridge

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint SecA
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

@[expose] def IsL24Sub {Q : Type} [Group Q] (S B : Subgroup Q) : Prop :=
  B ≠ ⊥ ∧ ⁅B, B⁆ = B ∧ S ≤ Subgroup.normalizer (B : Set Q) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) F)

@[expose] def FactBorelShape : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], Shape4 Q → ¬ IsPSL 3 2 2 Q →
    ∀ S : Subgroup Q, QuasithinUnique.IsSylowTwoOf S ⊤ →
      ∀ B₁ B₂ : Subgroup Q, B₁ ≠ B₂ → IsL24Sub S B₁ → IsL24Sub S B₂ →
        Subgroup.normalizer (B₁ : Set Q) ⊓ Subgroup.normalizer (B₂ : Set Q) ≤
            Subgroup.normalizer (S : Set Q) ∧
          Nat.card ↥(Subgroup.normalizer (S : Set Q)) = Nat.card ↥S * 9

@[expose] def FactParabTwo : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], Shape4 Q →
    ∀ S : Subgroup Q, QuasithinUnique.IsSylowTwoOf S ⊤ →
      ∀ B₁ B₂ B₃ : Subgroup Q, IsL24Sub S B₁ → IsL24Sub S B₂ → IsL24Sub S B₃ →
        (B₁ ≤ B₂ → B₁ = B₂) ∧ (B₁ = B₂ ∨ B₁ = B₃ ∨ B₂ = B₃)

@[expose] def FactNatPointSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₁ : Subgroup W, IsFlagW H P ⊥ (2 ^ n) 1 U₁ →
      ∀ D : Subgroup (MulAut W),
        QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (P : Set (MulAut W))) →
          (∀ w : W, w ≠ 1 → (∀ p ∈ P, p w = w) →
            w ∈ U₁ ∧ ∀ h ∈ H, h w = w → h ∈ stabW U₁) ∧
          ∃ d ∈ D, ∀ u ∈ U₁, u ≠ 1 → d u ≠ u

@[expose] def FactNatPointSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₁ : Subgroup W, IsFlagW H P ⊥ (2 ^ n) 1 U₁ →
      ∀ D : Subgroup (MulAut W),
        QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (P : Set (MulAut W))) →
          (∀ w : W, w ≠ 1 → (∀ p ∈ P, p w = w) →
            w ∈ U₁ ∧ ∀ h ∈ H, h w = w → h ∈ stabW U₁) ∧
          ∃ d ∈ D, ∀ u ∈ U₁, u ≠ 1 → d u ≠ u

@[expose] def FactNatPointG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₁ : Subgroup W, IsFlagW H P ⊥ (2 ^ n) 1 U₁ →
      ∀ D : Subgroup (MulAut W),
        QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (P : Set (MulAut W))) →
          (∀ w : W, w ≠ 1 → (∀ p ∈ P, p w = w) →
            w ∈ U₁ ∧ ∀ h ∈ H, h w = w → h ∈ stabW U₁) ∧
          ∃ d ∈ D, ∀ u ∈ U₁, u ≠ 1 → d u ≠ u

structure NatPointFacts : Prop where
  sl3 : FactNatPointSL3
  sp4 : FactNatPointSp4
  g2 : FactNatPointG2

@[expose] def FactL34NotL42 : Prop :=
  ∀ (X : Type) [Group X], IsPSL 3 2 2 X → ¬ IsPSL 4 2 1 X

end CFSG.Quasithin.Vol2.Ch11.SecS
