module

public import CFSG.Quasithin.Vol2.Ch11SecE43Out

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

@[expose] def FactOut2SL2 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 1 ≤ n → Nat.card F = 2 ^ n →
    ∀ (X : Type) [Group X], Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) F) → Out2Closed X

@[expose] def FactOut2L2p : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → 11 ≤ p → IsPSL 2 p 1 X → Out2Closed X

@[expose] def FactOut2Case1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (n : ℕ),
    (List11_1_1Two (↥K ⧸ CFSG.pCore 2 ↥K) n ∨
      (n = 2 ∧ List11_1_1Three (↥K ⧸ CFSG.pCore 2 ↥K))) →
    Case11_1_2One K → ⁅K, K⁆ = K → Out2Closed (↥K ⧸ CFSG.pCore 2 ↥K)

@[expose] def FactFixPointSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, SecA.IsFlagW H P ⊥ (2 ^ n) 1 U →
        ∀ w : W, (∀ p ∈ P, p w = w) → w ∈ U

@[expose] def FactFixPointSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, SecA.IsFlagW H P ⊥ (2 ^ n) 1 U →
        ∀ w : W, (∀ p ∈ P, p w = w) → w ∈ U

@[expose] def FactFixPointG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, SecA.IsFlagW H P ⊥ (2 ^ n) 1 U →
        ∀ w : W, (∀ p ∈ P, p w = w) → w ∈ U

structure Facts43 : Prop where
  out2SL2 : FactOut2SL2
  out2L2p : FactOut2L2p
  out2Case1 : FactOut2Case1
  fixSL3 : FactFixPointSL3
  fixSp4 : FactFixPointSp4
  fixG2 : FactFixPointG2

end CFSG.Quasithin.Vol2.Ch11.SecE
