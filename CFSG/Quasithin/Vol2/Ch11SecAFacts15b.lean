module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts15

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

section Defs

variable {W : Type*} [Group W]

@[expose] def RadicalFixes (H : Subgroup (MulAut W)) (Z U : Subgroup W) : Prop :=
  ∀ w : W, (∀ x : ↥(perfectCore (H ⊓ stabW U)), x ∈ CFSG.pCore 2 ↥(perfectCore (H ⊓ stabW U)) →
    (x : MulAut W) w * w⁻¹ ∈ Z) → w ∈ U

@[expose] def RadicalPoint (H : Subgroup (MulAut W)) (Z U : Subgroup W) : Prop :=
  ∀ τ : MulAut W, (∃ k : ℕ, τ ^ 2 ^ k = 1) → τ ∈ stabW Z → (∀ h ∈ H, τ * h * τ⁻¹ ∈ H) →
    (∀ x ∈ perfectCore (H ⊓ stabW U), τ * x * τ⁻¹ ∈ perfectCore (H ⊓ stabW U)) →
    (∀ x : ↥(perfectCore (H ⊓ stabW U)), ∃ y : ↥(perfectCore (H ⊓ stabW U)),
      y ∈ CFSG.pCore 2 ↥(perfectCore (H ⊓ stabW U)) ∧
        τ * (x : MulAut W) * τ⁻¹ = (y : MulAut W) * x) →
    ∀ u ∈ U, τ u * u⁻¹ ∈ Z

end Defs

@[expose] def FactRadicalFixedSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U → RadicalFixes H Z U

@[expose] def FactRadicalFixedSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U → RadicalFixes H Z U

@[expose] def FactRadicalFixedG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W)
      (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U → RadicalFixes H Z U

@[expose] def FactRadicalPointSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U → RadicalPoint H Z U

@[expose] def FactRadicalPointSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U → RadicalPoint H Z U

@[expose] def FactRadicalPointG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W)
      (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U → RadicalPoint H Z U

structure Facts15 : Prop where
  rankTwo : FactRankTwoLieSp4G2
  sylowSL3 : FactSylowLeviSL3
  sylowSp4 : FactSylowLeviSp4
  sylowG2 : FactSylowLeviG2
  pointCentSL3 : FactPointCentralizerSL3
  radFixSL3 : FactRadicalFixedSL3
  radFixSp4 : FactRadicalFixedSp4
  radFixG2 : FactRadicalFixedG2
  radPointSL3 : FactRadicalPointSL3
  radPointSp4 : FactRadicalPointSp4
  radPointG2 : FactRadicalPointG2

end CFSG.Quasithin.Vol2.Ch11.SecA
