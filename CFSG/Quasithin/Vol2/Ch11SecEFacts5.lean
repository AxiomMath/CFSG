module

public import CFSG.Quasithin.Background.E2Two
public import CFSG.Quasithin.H13.Statements
public import CFSG.Quasithin.Vol2.Ch11SecAFactsFlag

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

@[expose] def TorusPointConcl {W : Type*} [CommGroup W] (H : Subgroup (MulAut W)) (U : Subgroup W) :
    Prop :=
  ∀ h ∈ H, ∀ u ∈ U, u ≠ 1 → h u = u →
    (∀ k ∈ perfectCore (H ⊓ SecA.stabW U),
      h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore (H ⊓ SecA.stabW U))) →
    ∃ a : ℕ, h ^ 2 ^ a = 1

@[expose] def FactTorusPointSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, SecA.IsFlagW H P ⊥ (2 ^ n) 1 U → TorusPointConcl H U

@[expose] def FactTorusPointSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, SecA.IsFlagW H P ⊥ (2 ^ n) 1 U → TorusPointConcl H U

@[expose] def FactTorusPointG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, SecA.IsFlagW H P ⊥ (2 ^ n) 1 U → TorusPointConcl H U

@[expose] def CentLeviConcl {W : Type*} [CommGroup W] (H : Subgroup (MulAut W)) (U : Subgroup W)
    (n : ℕ) : Prop :=
  ∀ β : MulAut W, (∀ h ∈ H, β * h * β⁻¹ ∈ H) →
    (∀ k ∈ perfectCore (H ⊓ SecA.stabW U), β * k * β⁻¹ ∈ perfectCore (H ⊓ SecA.stabW U)) →
    (∀ k ∈ perfectCore (H ⊓ SecA.stabW U),
      β * k * β⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore (H ⊓ SecA.stabW U))) →
    (∃ m : ℕ, Odd m ∧ Nat.Coprime m (2 ^ n - 1) ∧ β ^ m = 1) → β = 1

@[expose] def FactCentLeviSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, SecA.IsFlagW H P ⊥ (2 ^ n) 1 U → CentLeviConcl H U n

@[expose] def FactCentLeviSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, SecA.IsFlagW H P ⊥ (2 ^ n) 1 U → CentLeviConcl H U n

@[expose] def FactCentLeviG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, SecA.IsFlagW H P ⊥ (2 ^ n) 1 U → CentLeviConcl H U n

@[expose] def FactBorelNotTwo : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X B : Subgroup Y) (m : ℕ), 2 ≤ m →
    (IsPSL 2 2 m ↥X ∨ IsSz m ↥X ∨ IsPSU 3 2 m ↥X ∨ IsPSL 3 2 m ↥X ∨ E2.IsSp4Prime m ↥X) →
    E2.IsBorelIn X B → ¬ IsPGroup 2 ↥B

structure Facts44 : Prop where
  torusSL3 : FactTorusPointSL3
  torusSp4 : FactTorusPointSp4
  torusG2 : FactTorusPointG2
  leviSL3 : FactCentLeviSL3
  leviSp4 : FactCentLeviSp4
  leviG2 : FactCentLeviG2
  borel : FactBorelNotTwo

end CFSG.Quasithin.Vol2.Ch11.SecE
