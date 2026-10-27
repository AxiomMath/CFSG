module

public import CFSG.Quasithin.Vol2.Ch11SecAFactsFlag
public import CFSG.Quasithin.Vol2.Ch11SecABasic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open SecA (IsFlagW stabW)

@[expose] def FactSolvPointG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W)
      (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₁ : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U₁ →
      ∀ S : Subgroup (MulAut W), S ≤ H ⊓ stabW U₁ →
        H ⊓ stabW U₁ ≤ Subgroup.normalizer (S : Set (MulAut W)) → Group.IsSolvable ↥S →
        (∀ s ∈ S, ∀ u ∈ U₁, s u * u⁻¹ ∈ Z) → IsPGroup 2 ↥S

@[expose] def SL2pMultFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P Q : Subgroup G) (p : ℕ), p.Prime → 5 ≤ p →
    ⁅K, K⁆ = K → Q ≤ P → P ≤ K → K ≤ Subgroup.normalizer (P : Set G) →
    K ≤ Subgroup.normalizer (Q : Set G) → ⁅P, K⁆ ≤ Q →
    (∃ φ : ↥K →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p), Function.Surjective φ ∧
      φ.ker = P.subgroupOf K) →
      P = Q

@[expose] def L2pSignalizerFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K L₁ R : Subgroup G) (p n : ℕ), p.Prime → 11 ≤ p →
    2 ≤ n → IsPSL 2 p 1 (↥K ⧸ CFSG.pCore 2 ↥K) → L₁ ≤ K → ⁅L₁, L₁⁆ = L₁ →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
    IsPGroup 2 R → R ≤ Subgroup.normalizer (K : Set G) → R ≤ Subgroup.normalizer (L₁ : Set G) →
    ⁅R, L₁⁆ ≤ pCoreOf 2 L₁ → ⁅R, K⁆ ≤ pCoreOf 2 K

end CFSG.Quasithin.Vol2.Ch11.SecD
