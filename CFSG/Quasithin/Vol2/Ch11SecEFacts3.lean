module

public import CFSG.Quasithin.Vol2.Ch11SecAFactsFlag
public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

@[expose] def ParInConcl {W : Type*} [CommGroup W] (H S : Subgroup (MulAut W)) (U : Subgroup W) :
    Prop :=
  ∀ s ∈ S, (∀ k ∈ perfectCore (H ⊓ SecA.stabW U),
    s * k * s⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore (H ⊓ SecA.stabW U))) → s ∈ H

@[expose] def FactParInSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, SecA.IsFlagW H P ⊥ (2 ^ n) 1 U →
      ∀ S : Subgroup (MulAut W), IsPGroup 2 S → (∀ s ∈ S, ∀ h ∈ H, s * h * s⁻¹ ∈ H) →
        S ≤ SecA.stabW U → NoGraphAutomorphism π S → ParInConcl H S U

@[expose] def FactParInSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, SecA.IsFlagW H P ⊥ (2 ^ n) 1 U →
      ∀ S : Subgroup (MulAut W), IsPGroup 2 S → (∀ s ∈ S, ∀ h ∈ H, s * h * s⁻¹ ∈ H) →
        S ≤ SecA.stabW U → NoGraphAutomorphismSp4 π S → ParInConcl H S U

@[expose] def FactParInG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ ⊥ π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U : Subgroup W, SecA.IsFlagW H P ⊥ (2 ^ n) 1 U →
      ∀ S : Subgroup (MulAut W), IsPGroup 2 S → (∀ s ∈ S, ∀ h ∈ H, s * h * s⁻¹ ∈ H) →
        S ≤ SecA.stabW U → ParInConcl H S U

structure ParInFacts : Prop where
  sl3 : FactParInSL3
  sp4 : FactParInSp4
  g2 : FactParInG2

@[expose] def SL2pSignalizerFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K L₁ R : Subgroup G) (p : ℕ), p.Prime → (p = 5 ∨ 11 ≤ p) →
    (∃ φ : ↥K →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p),
      Function.Surjective φ ∧ φ.ker = (oTwoTwoPrime K).subgroupOf K) →
    L₁ ≤ K → ⁅L₁, L₁⁆ = L₁ →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
    R ≤ Subgroup.normalizer (K : Set G) → R ≤ Subgroup.normalizer (L₁ : Set G) →
    ⁅R, L₁⁆ ≤ pCoreOf 2 L₁ → ⁅R, K⁆ ≤ oTwoTwoPrime K

@[expose] def FactCase1Comm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (n : ℕ),
    (List11_1_1Two (↥K ⧸ CFSG.pCore 2 ↥K) n ∨
      (n = 2 ∧ List11_1_1Three (↥K ⧸ CFSG.pCore 2 ↥K))) →
    Case11_1_2One K → ⁅K, K⁆ = K →
    ∀ r x : G, r ∈ Subgroup.normalizer (K : Set G) → x ∈ Subgroup.normalizer (K : Set G) →
      (∀ y ∈ K, r * y * r⁻¹ * y⁻¹ ∈ oTwoTwoPrime K) →
      (∃ k : ℕ, (r * x * r⁻¹ * x⁻¹) ^ 2 ^ k = 1) →
      ∀ y ∈ K, (r * x * r⁻¹ * x⁻¹) * y * (r * x * r⁻¹ * x⁻¹)⁻¹ * y⁻¹ ∈ pCoreOf 2 K

end CFSG.Quasithin.Vol2.Ch11.SecE
