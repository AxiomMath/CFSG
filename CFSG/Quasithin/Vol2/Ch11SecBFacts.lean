module

public import CFSG.Quasithin.Vol2.Ch11SecAFactsFlag
public import CFSG.Quasithin.Vol2.Ch11SecAFacts
public import CFSG.Quasithin.Vol2.Ch11StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

section Vocabulary

variable {W : Type*} [Group W]

@[expose] def ActsCyclicallyOn (S : Subgroup (MulAut W)) (U : Subgroup W) : Prop :=
  ∃ s₀ ∈ S, ∀ s ∈ S, ∃ k : ℤ, ∀ u ∈ U, s u = (s₀ ^ k) u

@[expose] def ActsRegularlyOn (S : Subgroup (MulAut W)) (U : Subgroup W) : Prop :=
  (∀ u ∈ U, ∀ w ∈ U, u ≠ 1 → w ≠ 1 → ∃ s ∈ S, s u = w) ∧
    ∀ s ∈ S, ∀ u ∈ U, u ≠ 1 → s u = u → ∀ w ∈ U, s w = w

end Vocabulary

@[expose] def FactPointSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P ⊥ (2 ^ n) 1 U →
        ActsCyclicallyOn (H ⊓ stabW U) U ∧ ActsRegularlyOn (H ⊓ stabW U) U

@[expose] def FactPointSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P ⊥ (2 ^ n) 1 U →
        ActsCyclicallyOn (H ⊓ stabW U) U ∧ ActsRegularlyOn (H ⊓ stabW U) U

@[expose] def FactPointG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P ⊥ (2 ^ n) 1 U →
        ActsCyclicallyOn (H ⊓ stabW U) U ∧ ActsRegularlyOn (H ⊓ stabW U) U

@[expose] def FactPointTSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P ⊥ (2 ^ n) 1 U →
      ∀ S : Subgroup (MulAut W), IsPGroup 2 S → (∀ s ∈ S, ∀ h ∈ H, s * h * s⁻¹ ∈ H) →
        S ≤ stabW U → NoGraphAutomorphism π S → ActsCyclicallyOn S U

@[expose] def FactPointTSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P ⊥ (2 ^ n) 1 U →
      ∀ S : Subgroup (MulAut W), IsPGroup 2 S → (∀ s ∈ S, ∀ h ∈ H, s * h * s⁻¹ ∈ H) →
        S ≤ stabW U → NoGraphAutomorphismSp4 π S → ActsCyclicallyOn S U

@[expose] def FactPointTG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P ⊥ (2 ^ n) 1 U →
      ∀ S : Subgroup (MulAut W), IsPGroup 2 S → (∀ s ∈ S, ∀ h ∈ H, s * h * s⁻¹ ∈ H) →
        S ≤ stabW U → ActsCyclicallyOn S U

@[expose] def ParConcl {W : Type*} [CommGroup W] (H S : Subgroup (MulAut W)) (U : Subgroup W) :
    Prop :=
  (∀ h ∈ perfectCore (H ⊓ stabW U), ∀ u ∈ U, h u = u) ∧
    ∀ s ∈ S, (∀ k ∈ perfectCore (H ⊓ stabW U),
      s * k * s⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore (H ⊓ stabW U))) → ∀ u ∈ U, s u = u

@[expose] def FactParSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ Z π → fixV H = Z → commV H = ⊤ →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U →
      ∀ S : Subgroup (MulAut W), IsPGroup 2 S → (∀ s ∈ S, ∀ h ∈ H, s * h * s⁻¹ ∈ H) →
        S ≤ stabW U → NoGraphAutomorphism π S → ParConcl H S U

@[expose] def FactParSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π → fixV H = Z → commV H = ⊤ →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U →
      ∀ S : Subgroup (MulAut W), IsPGroup 2 S → (∀ s ∈ S, ∀ h ∈ H, s * h * s⁻¹ ∈ H) →
        S ≤ stabW U → NoGraphAutomorphismSp4 π S → ParConcl H S U

@[expose] def FactParG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π → fixV H = Z →
      commV H = ⊤ →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U →
      ∀ S : Subgroup (MulAut W), IsPGroup 2 S → (∀ s ∈ S, ∀ h ∈ H, s * h * s⁻¹ ∈ H) →
        S ≤ stabW U → ParConcl H S U

structure PointFacts : Prop where
  pointSL3 : FactPointSL3
  pointSp4 : FactPointSp4
  pointG2 : FactPointG2
  pointTSL3 : FactPointTSL3
  pointTSp4 : FactPointTSp4
  pointTG2 : FactPointTG2
  parSL3 : FactParSL3
  parSp4 : FactParSp4
  parG2 : FactParG2

end CFSG.Quasithin.Vol2.Ch11.SecB
