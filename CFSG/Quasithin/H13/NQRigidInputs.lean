module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCollapse
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Quasithin.H13.NQRigidConjugate
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.QuasithinUnique.Setup.SL2Modules (repOfSubgroup)
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups Pointwise

section Lattice

variable {H : Type*} [Group H]

@[expose] def frattiniPreimage (X : Subgroup H) (Q : Subgroup X) [Q.Normal] : Subgroup H :=
  ((frattini (X ⧸ Q)).comap (QuotientGroup.mk' Q)).map X.subtype

@[expose] def IsFrattiniLatticeIrreducible (X A : Subgroup H) (Q : Subgroup X) [Q.Normal] :
    Prop :=
  ∀ Y : Subgroup H, frattiniPreimage X Q ≤ Y → Y ≤ X → A ≤ normalizer (Y : Set H) →
    Y = frattiniPreimage X Q ∨ Y = X

end Lattice

@[expose] def StmtEscapingComponentAction : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N : Subgroup H) [N.Normal], Group.IsSolvable N →
    ∀ X : Subgroup H, (∀ D : Subgroup X, D.Normal → D.index ≠ 2) →
    (∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r (H ⧸ N) ≤ 2) →
    ∀ K : Subgroup H, CFSG.IsCComponent K → CFSG.IsComponent (K.map (QuotientGroup.mk' N)) →
      X ≤ normalizer (K : Set H) ∧
        (¬ K.map (QuotientGroup.mk' N) ≤
            normalizer ((X.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N)) →
          ⁅K, X⁆ = K)

@[expose] def StmtOuterRankContainment : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ), p.Prime → p ≠ 2 → CFSG.pRank p H ≤ 2 →
    ∀ (C : Subgroup H) [C.Normal], IsPGroup 2 C →
    ∀ K : Subgroup H, CFSG.IsCComponent K → CFSG.IsComponent (K.map (QuotientGroup.mk' C)) →
      ¬ p ∣ Nat.card (center (K.map (QuotientGroup.mk' C))) →
      CFSG.pRank p (Outer (K.map (QuotientGroup.mk' C))) ≤ 1 →
    ∀ (X A : Subgroup H) (Q : Subgroup X) [Q.Normal], X ≤ A →
      A ≤ normalizer (K : Set H) → A ≤ normalizer ((Q.map X.subtype : Subgroup H) : Set H) →
      A ≤ normalizer (X : Set H) → IsPGroup 2 Q → (∀ x : X, x ^ p ∈ Q) → NoPQuotient 2 X →
      p ^ 2 ≤ Nat.card ((X ⧸ Q) ⧸ frattini (X ⧸ Q)) → IsFrattiniLatticeIrreducible X A Q →
      ⁅K.map (QuotientGroup.mk' C), X.map (QuotientGroup.mk' C)⁆ ≠ ⊥ →
      (∀ x ∈ X.map (QuotientGroup.mk' C), ∃ j ∈ K.map (QuotientGroup.mk' C),
          ∀ y ∈ K.map (QuotientGroup.mk' C), x * y * x⁻¹ = j * y * j⁻¹) ∧
        CFSG.pRank p (K.map (QuotientGroup.mk' C)) = 2 ∧ K.Normal ∧ X ≤ K

@[expose] def StmtPairContainment : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ), p.Prime → p ≠ 2 → CFSG.pRank p H ≤ 2 →
    ∀ (C : Subgroup H) [C.Normal], IsPGroup 2 C →
    ∀ K₁ K₂ : Subgroup H, CFSG.IsCComponent K₁ → K₂ ≠ K₁ →
      (∀ h : H, CFSG.conjugate K₁ h = K₁ ∨ CFSG.conjugate K₁ h = K₂) →
      (∃ h : H, CFSG.conjugate K₁ h = K₂) →
      CFSG.IsComponent (K₁.map (QuotientGroup.mk' C)) →
      ¬ p ∣ Nat.card (center (K₁.map (QuotientGroup.mk' C))) →
      ¬ p ∣ Nat.card (commutator (Outer (K₁.map (QuotientGroup.mk' C)))) →
    ∀ (X A : Subgroup H) (Q : Subgroup X) [Q.Normal], X ≤ A →
      A ≤ normalizer ((Q.map X.subtype : Subgroup H) : Set H) → A ≤ normalizer (X : Set H) →
      IsPGroup 2 Q → (∀ x : X, x ^ p ∈ Q) → NoPQuotient 2 X →
      p ^ 2 ≤ Nat.card ((X ⧸ Q) ⧸ frattini (X ⧸ Q)) → IsFrattiniLatticeIrreducible X A Q →
      ⁅(K₁ ⊔ K₂).map (QuotientGroup.mk' C), X.map (QuotientGroup.mk' C)⁆ ≠ ⊥ →
      X ≤ K₁ ⊔ K₂ ∧ (K₁ ⊔ K₂).Normal ∧
        (∀ x ∈ X.map (QuotientGroup.mk' C), ∃ j ∈ (K₁ ⊔ K₂).map (QuotientGroup.mk' C),
          ∀ y ∈ (K₁ ⊔ K₂).map (QuotientGroup.mk' C), x * y * x⁻¹ = j * y * j⁻¹) ∧
        CFSG.pRank p ((K₁ ⊔ K₂).map (QuotientGroup.mk' C)) = 2 ∧
        CFSG.pRank p (K₁.map (QuotientGroup.mk' C)) = 1 ∧
        CFSG.pRank p (K₂.map (QuotientGroup.mk' C)) = 1

@[expose] def StmtOrdinaryEvenSymplecticFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L K X : Subgroup G), Group.IsPerfect L →
    CFSG.IsQuasisimple K → X ≤ L → X ≤ K → (X.subgroupOf L).Normal →
    ∀ p : ℕ, p.Prime → 5 ≤ p → CFSG.pCore 2 X ≠ ⊥ → IsPGroup p (X ⧸ CFSG.pCore 2 X) →
    Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p →
    Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2 →
    IsFrattiniIrreducible X L → NoPQuotient 2 X →
    ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)) →
    ∀ f : ℕ, 2 ≤ f →
      ¬ StatedClassicalModel ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .PSp 2 2 f

@[expose] def StmtNoncyclicLocalSylowFourEven : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ), p.Prime → 5 ≤ p → ∀ (D : Subgroup H) (Q : Sylow 2 H),
    (Q : Subgroup H) ≤ D → ∀ (K : Subgroup H) [K.Normal] (X : Subgroup H), X ≤ D →
    (X.subgroupOf D).Normal → X ≤ K → IsPGroup p (X ⧸ CFSG.pCore 2 X) →
    ¬ IsCyclic (((Q : Subgroup H).subgroupOf (normalizer (X : Set H))).map
      (normalizerFrattiniConj X)) →
    ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)) →
    (∀ f : ℕ, 2 ≤ f → ¬ StatedClassicalModel
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .PSp 2 2 f) ∧
      (∀ f : ℕ, 2 ≤ f → ¬ ChevalleyExceptionalModel
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .G2 2 f) ∧
      (∀ f : ℕ, 1 ≤ f → ¬ ChevalleyExceptionalModel
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .trialityD4 2 f) ∧
      ∀ a : ℕ, 1 ≤ a → ¬ ReeTitsModel
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .twistedF4 2 (2 * a + 1)

@[expose] def StmtFourDivisibilityFields : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ), p.Prime → 5 ≤ p → ∀ (D : Subgroup H) (Q : Sylow 2 H),
    (Q : Subgroup H) ≤ D → ∀ (K : Subgroup H) [K.Normal] (X : Subgroup H), X ≤ D →
    (X.subgroupOf D).Normal → X ≤ K → IsPGroup p (X ⧸ CFSG.pCore 2 X) →
    4 ∣ Nat.card (((Q : Subgroup H).subgroupOf (normalizer (X : Set H))).map
      (normalizerFrattiniConj X)) →
    ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)) →
    (∀ f : ℕ, 2 ≤ f → StatedClassicalModel
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .PSp 2 2 f → Even f) ∧
      (∀ f : ℕ, 2 ≤ f → ChevalleyExceptionalModel
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .G2 2 f → 4 ∣ f) ∧
      ∀ f : ℕ, 1 ≤ f → ChevalleyExceptionalModel
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .trialityD4 2 f → 4 ∣ f

@[expose] def StmtCPUOffenderSection : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (R : Subgroup H), IsPGroup 2 R →
    R = (CFSG.pCore 2 (normalizer (R : Set H))).map (normalizer (R : Set H)).subtype →
    ∀ K : Subgroup H, CFSG.IsCComponent K → CFSG.generalizedFitting K = CFSG.pCore 2 K →
    CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K) → R ≤ normalizer (K : Set H) →
    ∀ M : Subgroup H, ¬ K ≤ M →
    (∀ D : Subgroup R, D.Characteristic → D ≠ ⊥ →
      normalizer ((D.map R.subtype : Subgroup H) : Set H) ≤ M) →
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W) (_ : Nontrivial W)
      (L₁ B₁ : Subgroup (Module.End (ZMod 2) W)ˣ),
      CFSG.IsQuasisimple L₁ ∧ (repOfSubgroup L₁).IsIrreducible ∧
        CFSG.IsElementaryAbelian 2 B₁ ∧ B₁ ≠ ⊥ ∧
        B₁ ≤ normalizer (L₁ : Set (Module.End (ZMod 2) W)ˣ) ∧
        (∀ a ∈ B₁, ∀ b ∈ B₁, ∀ w : W, (b.val - 1) ((a.val - 1) w) = 0) ∧
        Nat.card W ≤ Nat.card B₁ * Nat.card {w : W // ∀ b ∈ B₁, b.val w = w} ∧
        Nonempty (L₁ ⧸ center L₁ ≃* (K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))

@[expose] def StmtCPUShortBlock : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (R : Subgroup H), IsPGroup 2 R →
    R = (CFSG.pCore 2 (normalizer (R : Set H))).map (normalizer (R : Set H)).subtype →
    ∀ K : Subgroup H, CFSG.IsCComponent K → CFSG.generalizedFitting K = CFSG.pCore 2 K →
    CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K) → R ≤ normalizer (K : Set H) →
    ∀ M : Subgroup H, ¬ K ≤ M →
    (∀ D : Subgroup R, D.Characteristic → D ≠ ⊥ →
      normalizer ((D.map R.subtype : Subgroup H) : Set H) ≤ M) →
    ∀ n : ℕ, 3 ≤ n → ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = 2 ^ n →
    Nonempty ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K) ≃* SL(2, F)) →
    CFSG.QuasithinUnique.IsShort2 K

@[expose] def StmtJ4SingleComponent : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (D K X : Subgroup H), D ≤ normalizer (K : Set H) →
    X ≤ D → (X.subgroupOf D).Normal → X ≤ K → ∀ p : ℕ, p.Prime → 5 ≤ p →
    IsPGroup p (X ⧸ CFSG.pCore 2 X) →
    p ^ 2 ≤ Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) →
    IsFrattiniIrreducible X D →
    ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)) →
    ∀ P B : Subgroup H, IsSylowOf p P X → IsSylowOf 2 B K →
      (P : Set H) * (B : Set H) = (B : Set H) * (P : Set H) →
      IsEmpty ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K) ≃* NativeSporadic.J4)

@[expose] def StmtTitsSylowProduct : Prop :=
  ∀ (K S : Type) [Group K] [Group S] [Finite K] [Finite S] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ σ : K →* S, Function.Surjective σ → ¬ p ∣ Nat.card σ.ker →
    ∀ P : Subgroup K, IsPGroup p P → ¬ IsCyclic P → ∀ B : Sylow 2 K,
      (P : Set K) * ((B : Subgroup K) : Set K) = ((B : Subgroup K) : Set K) * (P : Set K) →
      ¬ ReeTitsModel S .Tits 2 1

@[expose] def StmtOuterDerivedCoprime : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.SectionRank.IsSQTKCat H → ∀ J : Subgroup H,
    CFSG.IsComponent J → (∃ h : H, CFSG.conjugate J h ≠ J) →
    ∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ → ¬ ℓ ∣ Nat.card (commutator (Outer J))

end CFSG.Quasithin.H13.NQRigid
