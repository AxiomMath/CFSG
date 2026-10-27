module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.H13.NQRigidModule
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL stabilizer proj)
open CFSG.QuasithinUnique.Setup.SL2Modules (evenWeight permAct)
open Equiv

@[expose] def OblRigidWholeModule : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M → QTNQExplicitModule L M

@[expose] def RigidSingleCPUConfig {G : Type} [Group G] [Finite G] (T L M : Subgroup G) (p : ℕ)
    (X : Subgroup G) (v : G) (K : Subgroup (centralizer ({v} : Set G))) : Prop :=
  QTNQ T L M ∧ QTNQExplicitModule L M ∧ p.Prime ∧ 5 ≤ p ∧
    X ≤ L ∧ (X.subgroupOf L).Characteristic ∧ X ≤ (CFSG.solvableRadical L).map L.subtype ∧
    CFSG.pCore 2 X ≠ ⊥ ∧ normalizer (X : Set G) = M ∧ NoPQuotient 2 X ∧
    Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p ∧ CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2 ∧
    Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2 ∧
    (∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1) ∧
    IsFrattiniIrreducible X L ∧
    v ∈ qtnqU L M ∧ v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ M ∧
    IsSylowOf 2 (T ⊓ centralizer {v}) (M ⊓ centralizer {v}) ∧
    IsSylowOf 2 (T ⊓ centralizer {v}) (centralizer {v}) ∧
    CFSG.IsCComponent K ∧ K.Normal ∧ X.subgroupOf (centralizer ({v} : Set G)) ≤ K ∧
    ¬ K ≤ (M ⊓ centralizer {v}).subgroupOf (centralizer ({v} : Set G)) ∧
    CFSG.generalizedFitting K = CFSG.pCore 2 K ∧ CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K)

@[expose] def OblRigidCPUEvenLinearThreeParabolic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G) (p : ℕ) (X : Subgroup G) (v : G)
    (K : Subgroup (centralizer ({v} : Set G))), RigidSingleCPUConfig T L M p X v K →
    ∀ f : ℕ, 3 ≤ f →
    StatedClassicalModel ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .PSL 3 2 f →
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ f ∧
      ∃ φ : K →* projectiveSL 3 k, ¬ p ∣ Nat.card φ.ker ∧
        ∃ E : Submodule k (Fin 3 → k), (Module.finrank k E = 1 ∨ Module.finrank k E = 2) ∧
          ((((M ⊓ centralizer {v}).subgroupOf (centralizer ({v} : Set G))) ⊓ K).subgroupOf
            K).map φ = (stabilizer E).map (proj 3 k)

@[expose] def OblRigidCPUSymplecticFourDeleted : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G) (p : ℕ) (X : Subgroup G) (v : G)
    (K : Subgroup (centralizer ({v} : Set G))), RigidSingleCPUConfig T L M p X v K →
    ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω], Fintype.card Ω = 5 →
    ∀ (β : (L ⧸ CFSG.solvableRadical L) ≃* alternatingGroup Ω)
      (θ : Additive (qtnqU L M) ≃+ evenWeight Ω),
      (∀ (l : L) (x y : qtnqU L M), (y : G) = (l : G) * x * (l : G)⁻¹ →
        (θ (Additive.ofMul y) : Ω → ZMod 2) =
          permAct (β (l : L ⧸ CFSG.solvableRadical L) : Perm Ω) (θ (Additive.ofMul x))) →
    ∀ hv : v ∈ qtnqU L M,
      (Finset.univ.filter fun ω => (θ (Additive.ofMul ⟨v, hv⟩) : Ω → ZMod 2) ω ≠ 0).card = 2 →
    ∀ f : ℕ, 2 ≤ f → Even f →
      ¬ StatedClassicalModel ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .PSp 2 2 f

end CFSG.Quasithin.H13.NQRigid
