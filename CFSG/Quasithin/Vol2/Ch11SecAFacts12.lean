module

public import CFSG.Quasithin.Vol2.Ch11SecSFactsCartan
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch11SecSFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint SecS
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

section Vocabulary

variable {W : Type*} [Group W]

@[expose] def CartanPoint (H : Subgroup (MulAut W)) (Z U₁ : Subgroup W)
    (D : Subgroup (MulAut W)) : Prop :=
  ∀ d ∈ centW D (gammaW H U₁), (∀ u ∈ U₁, d u * u⁻¹ ∈ Z) → d = 1

end Vocabulary

@[expose] def FactCartanPointSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₁ : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U₁ →
      ∀ D : Subgroup (MulAut W),
        QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (P : Set (MulAut W))) →
          CartanPoint H Z U₁ D

@[expose] def FactCartanPointSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₁ : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U₁ →
      ∀ D : Subgroup (MulAut W),
        QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (P : Set (MulAut W))) →
          CartanPoint H Z U₁ D

@[expose] def FactCartanPointG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W)
      (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₁ : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U₁ →
      ∀ D : Subgroup (MulAut W),
        QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (P : Set (MulAut W))) →
          CartanPoint H Z U₁ D

@[expose] def FactList2Table : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → List11_1_1Two X n →
    CFSG.IsQuasisimple X ∧ Nat.card (Subgroup.center X) ∣ 3 ∧
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)

@[expose] def FactList2PSL3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], List11_1_1Two X 2 →
    ∀ (s : Bool) (p e : ℕ), p.Prime → 1 ≤ e → IsPSLEps3 s p e X → s = true ∧ p = 2 ∧ e = 2

structure Facts12 : Prop where
  pointSL3 : FactCartanPointSL3
  pointSp4 : FactCartanPointSp4
  pointG2 : FactCartanPointG2
  table : FactList2Table
  psl3 : FactList2PSL3

end CFSG.Quasithin.Vol2.Ch11.SecA
