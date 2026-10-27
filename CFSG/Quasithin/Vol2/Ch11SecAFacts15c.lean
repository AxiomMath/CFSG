module

public import CFSG.Quasithin.Vol2.Ch11SecAFactsFlag

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

section Defs

variable {W : Type*} [Group W]

@[expose] def RadicalInner (H : Subgroup (MulAut W)) (Z U : Subgroup W) : Prop :=
  ∀ τ : MulAut W, (∃ k : ℕ, τ ^ 2 ^ k = 1) → τ ∈ stabW Z → (∀ h ∈ H, τ * h * τ⁻¹ ∈ H) →
    (∀ x ∈ perfectCore (H ⊓ stabW U), τ * x * τ⁻¹ ∈ perfectCore (H ⊓ stabW U)) →
    (∀ x : ↥(perfectCore (H ⊓ stabW U)), ∃ y : ↥(perfectCore (H ⊓ stabW U)),
      y ∈ CFSG.pCore 2 ↥(perfectCore (H ⊓ stabW U)) ∧
        τ * (x : MulAut W) * τ⁻¹ = (y : MulAut W) * x) →
    ∃ y : ↥(perfectCore (H ⊓ stabW U)), y ∈ CFSG.pCore 2 ↥(perfectCore (H ⊓ stabW U)) ∧
      ∀ h ∈ H, τ * h * τ⁻¹ = (y : MulAut W) * h * (y : MulAut W)⁻¹

@[expose] def PointTorus (H : Subgroup (MulAut W)) (Z U : Subgroup W) : Prop :=
  ∃ d ∈ H ⊓ stabW U,
    (∀ h ∈ H ⊓ stabW U, ∃ k : ℕ, h * (d ^ k)⁻¹ ∈ perfectCore (H ⊓ stabW U)) ∧
    (∃ m : ℕ, Odd m ∧ d ^ m ∈ perfectCore (H ⊓ stabW U)) ∧
    ∀ u ∈ U, ∀ w ∈ U, u ∉ Z → w ∉ Z → ∃ k : ℕ, (d ^ k) u * w⁻¹ ∈ Z

@[expose] def RadicalCocycle (H : Subgroup (MulAut W)) (Z U : Subgroup W) : Prop :=
  ∀ d : ↥H → W, (∀ g h : ↥H, d (g * h) * ((g : MulAut W) (d h) * d g)⁻¹ ∈ Z) →
    (∀ (x : ↥H) (y : ↥(perfectCore (H ⊓ stabW U))),
      y ∈ CFSG.pCore 2 ↥(perfectCore (H ⊓ stabW U)) → (y : MulAut W) = x → d x ∈ Z) →
    ∃ u ∈ U, ∀ g : ↥H, d g * ((g : MulAut W) u * u⁻¹)⁻¹ ∈ Z

end Defs

@[expose] def FactRadicalInnerSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U → RadicalInner H Z U

@[expose] def FactRadicalInnerSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U → RadicalInner H Z U

@[expose] def FactPointTorusSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U → PointTorus H Z U

@[expose] def FactPointTorusSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U → PointTorus H Z U

@[expose] def FactRadicalCocycleSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z 4 1 U → RadicalCocycle H Z U

structure Facts15c : Prop where
  innerSL3 : FactRadicalInnerSL3
  innerSp4 : FactRadicalInnerSp4
  torusSL3 : FactPointTorusSL3
  torusSp4 : FactPointTorusSp4
  cocycleSp4 : FactRadicalCocycleSp4

end CFSG.Quasithin.Vol2.Ch11.SecA
