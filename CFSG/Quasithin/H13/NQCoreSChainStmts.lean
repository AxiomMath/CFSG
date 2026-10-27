module

public import CFSG.Quasithin.H13.NQCoreCanonicalResidual

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure SCNormalBranch (T D X H : Subgroup G) (K : Subgroup ↥H) (p : ℕ) : Prop where
  ccomp : CFSG.IsCComponent K
  isLocal : quasithinIsLocal T (K.map H.subtype)
  normal : K.Normal
  not_le : ¬ K.map H.subtype ≤ normalizer (D : Set G)
  genFitting : CFSG.generalizedFitting ↥K = CFSG.pCore 2 ↥K
  quasi : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)
  comp_e : CFSG.IsComponent (K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))
  core_inf : K ⊓ CFSG.pCore 2 ↥H = (CFSG.pCore 2 ↥K).map K.subtype
  card_center : Nat.card (center ↥(K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))) = 1 ∨
    Nat.card (center ↥(K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))) = 3
  escapes_e : ¬ K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ≤
    normalizer (((X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) :
      Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H))
  le : X.subgroupOf H ≤ K
  comm_eq : ⁅K, X.subgroupOf H⁆ = K
  core_le_normalizer : (pCoreOf 2 (X ⊔ T)).subgroupOf H ≤ normalizer (K : Set ↥H)
  pRank : CFSG.pRank p (K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) = 2

structure SCPairBranch (T D X P H : Subgroup G) (K : Subgroup ↥H) (t : ↥H) (p : ℕ) : Prop where
  ccomp : CFSG.IsCComponent K
  isLocal : quasithinIsLocal T (K.map H.subtype)
  mem : (t : G) ∈ T ⊓ normalizer (P : Set G)
  ne : CFSG.conjugate K t ≠ K
  conj : ∀ g : ↥H, CFSG.conjugate K g = K ∨ CFSG.conjugate K g = CFSG.conjugate K t
  not_le : ¬ K.map H.subtype ≤ normalizer (D : Set G)
  genFitting : CFSG.generalizedFitting ↥K = CFSG.pCore 2 ↥K
  quasi : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)
  comp_e : CFSG.IsComponent (K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))
  comp_e_conj : CFSG.IsComponent ((CFSG.conjugate K t).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))
  core_inf : K ⊓ CFSG.pCore 2 ↥H = (CFSG.pCore 2 ↥K).map K.subtype
  card_center : Nat.card (center ↥(K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))) = 1 ∨
    Nat.card (center ↥(K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))) = 3
  escapes_e : ¬ K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ≤
    normalizer (((X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) :
      Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H))
  normal_left : (K.subgroupOf (K ⊔ CFSG.conjugate K t)).Normal
  normal_right : ((CFSG.conjugate K t).subgroupOf (K ⊔ CFSG.conjugate K t)).Normal
  normal_sup : (K ⊔ CFSG.conjugate K t).Normal
  le_sup : X.subgroupOf H ≤ K ⊔ CFSG.conjugate K t
  le_normalizer :
    X.subgroupOf H ≤ normalizer (K : Set ↥H) ⊓ normalizer (CFSG.conjugate K t : Set ↥H)
  comm_eq : ⁅K, X.subgroupOf H⁆ = K
  core_le_normalizer : (pCoreOf 2 (X ⊔ T)).subgroupOf H ≤
    normalizer (K : Set ↥H) ⊓ normalizer (CFSG.conjugate K t : Set ↥H)
  pRank_K : CFSG.pRank p ↥K = 1
  pRank_conj : CFSG.pRank p ↥(CFSG.conjugate K t) = 1
  pRank_S : CFSG.pRank p (K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) = 1
  pRank_S₂ : CFSG.pRank p ((CFSG.conjugate K t).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) = 1
  pRank_central : ∀ r : ℕ, r.Prime → r ≠ 2 →
    CFSG.pRank r (↥(K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) ⧸
      center ↥(K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))) ≤ 1
  elemAbelian : CFSG.IsElementaryAbelian p (X ⧸ CFSG.pCore 2 X) ∧
    Nat.card (X ⧸ CFSG.pCore 2 X) = p ^ 2
  eq_sup : P.subgroupOf H ⊓ K ⊔ P.subgroupOf H ⊓ CFSG.conjugate K t = P.subgroupOf H
  inf_eq_bot : P.subgroupOf H ⊓ K ⊓ (P.subgroupOf H ⊓ CFSG.conjugate K t) = ⊥
  card_left : Nat.card (P.subgroupOf H ⊓ K : Subgroup ↥H) = p
  card_right : Nat.card (P.subgroupOf H ⊓ CFSG.conjugate K t : Subgroup ↥H) = p

structure SCSetup (T D X : Subgroup G) (p : ℕ) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : quasithinIsQTKECat G
  sylow : quasithinIsSylowTwo T
  maximal_local : quasithinIsMaximalLocal T D
  faithful_local : quasithinIsFaithfulLocal T D
  le_normalizer : T ≤ normalizer (D : Set G)
  not_quasisimple : ¬ CFSG.IsQuasisimple (↥D ⧸ CFSG.pCore 2 ↥D)
  prime : p.Prime
  five_le : 5 ≤ p
  ambient : SNAmbient T D
  canonical : SNCanonical T D X p

@[expose] def StmtSCNormalExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T D X H : Subgroup G) (K : Subgroup ↥H) (p : ℕ),
    SCSetup T D X p →
    quasithinIsMaxTwoLocal H → X ⊔ T ≤ H → ¬ (X.subgroupOf H).Normal →
    ¬ SCNormalBranch T D X H K p

@[expose] def StmtSCPairedExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T D X P H : Subgroup G) (K : Subgroup ↥H) (t : ↥H) (p : ℕ),
    SCSetup T D X p → quasithinIsMaxTwoLocal H → X ⊔ T ≤ H → ¬ (X.subgroupOf H).Normal →
    IsSylowOf p P X → ¬ SCPairBranch T D X P H K t p

@[expose] def StmtSCComponentOrbits : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T D X P H : Subgroup G) (p : ℕ), SCSetup T D X p →
    quasithinIsMaxTwoLocal H → X ⊔ T ≤ H → ¬ (X.subgroupOf H).Normal → IsSylowOf p P X →
    pCoreOf 2 H ≠ ⊥ ∧ CFSG.SectionRank.IsSQTKCat ↥H ∧ CharTwo H ∧
      H ⊓ normalizer (X : Set G) = H ⊓ normalizer (D : Set G) ∧
      H ⊓ normalizer (D : Set G) < H ∧ pCoreOf 2 H ≤ pCoreOf 2 (X ⊔ T) ∧
      P ⊔ T = X ⊔ T ∧ (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G) ∧
      T = pCoreOf 2 X ⊔ (T ⊓ normalizer (P : Set G)) ∧
      ((CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H)).comap
          (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype ≤ H ⊓ normalizer (D : Set G) ∧
      IsCyclic ↥(CFSG.pCore p (↥H ⧸ CFSG.pCore 2 ↥H)) ∧
      ⁅modO2Image H X, CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H)⁆ = ⊥ ∧
      ∃ K : Subgroup ↥H, SCNormalBranch T D X H K p ∨ ∃ t : ↥H, SCPairBranch T D X P H K t p

theorem every_maximal_overgroup_normalizes_of (hO : StmtSCComponentOrbits)
    (hN : StmtSCNormalExclusion) (hP : StmtSCPairedExclusion) {T D X H : Subgroup G} {p : ℕ}
    (hS : SCSetup T D X p) (hH : quasithinIsMaxTwoLocal H) (hXTH : X ⊔ T ≤ H) :
    (X.subgroupOf H).Normal := by
  by_contra hXn
  have : Fact p.Prime := ⟨hS.prime⟩
  obtain ⟨P, hP'⟩ := CFSG.ABGLocalTools.exists_isSylowOf p X
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, K, hK⟩ := hO G T D X P H p hS hH hXTH hXn hP'
  rcases hK with hK | ⟨t, hK⟩
  · exact hN G T D X H K p hS hH hXTH hXn hK
  · exact hP G T D X P H K t p hS hH hXTH hXn hP' hK

theorem unique_maximal_overgroup_of (hO : StmtSCComponentOrbits) (hN : StmtSCNormalExclusion)
    (hP : StmtSCPairedExclusion) {T D X : Subgroup G} {p : ℕ} (hS : SCSetup T D X p) :
    U3.UniqueMaxTwoLocal (X ⊔ T) (normalizer (D : Set G)) := by
  have hJ := hS.ambient.unique.1
  have hXT : X ⊔ T ≤ normalizer (D : Set G) :=
    sup_le (hS.canonical.le.trans le_normalizer) hS.le_normalizer
  refine ⟨hJ, hXT, fun H hH hXTH => ?_⟩
  have hn := every_maximal_overgroup_normalizes_of hO hN hP hS hH hXTH
  have hHX : H ≤ normalizer (X : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (le_sup_left.trans hXTH)).mp hn
  rw [← hS.canonical.normalizer_eq] at hHX
  exact (hH.2 _ hJ.1 hHX).symm

end CFSG.Quasithin.H13.NQCore
