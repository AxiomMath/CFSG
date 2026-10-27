module

public import CFSG.Quasithin.EmptyFaithful.S1469Ctx
public import CFSG.Quasithin.Background.C1GNBlocks
public import CFSG.Quasithin.Background.C2Seven
public import CFSG.Quasithin.Background.F6Cat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def IsBlockProduct (I S : Subgroup G) (r : ℕ) (K : Fin r → Subgroup G) : Prop :=
  1 ≤ r ∧ r ≤ 2 ∧ (∀ i, IsChi0Block I (K i)) ∧ (∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥) ∧
    I = S ⊔ ⨆ i, K i ∧ (∀ i j, ∃ t ∈ S, B6.conjSub t (K i) = K j) ∧
    (∀ t ∈ S, ∀ i, ∃ j, B6.conjSub t (K i) = K j)

@[expose] def z0Of1469 (Iz K₁ K₂ : Subgroup G) : Subgroup G :=
  centerOf (pCoreOf 2 (oTwoUpper Iz ⊓ K₁) ⊔ pCoreOf 2 (oTwoUpper Iz ⊓ K₂))

@[expose] def dOf1469 (T I K₁ K₂ : Subgroup G) : Subgroup G :=
  T ⊓ I ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G)

@[expose] def lD1469 (T M D : Subgroup G) : Subgroup G :=
  oTwoUpper (yOfL22 T M ⊓ Subgroup.normalizer (D : Set G))

structure Ctx1469A5 (T M H : Subgroup G) (u : G) (I K₁ K₂ : Subgroup G) (ρ : G) : Prop where
  ctx : Ctx1469 T M H u I
  charTwo : CharTwo I
  blocks : IsBlockProduct I (T ⊓ I) 2 ![K₁, K₂]
  a5 : IsAltType K₁ 5 ∧ IsAltType K₂ 5
  not_le : ¬ K₁ ≤ I ⊓ mcOf T
  rho : ρ ∈ T ∧ ρ ∈ Subgroup.normalizer ((T ⊓ I : Subgroup G) : Set G) ∧ ρ ∉ T ⊓ I ∧
    ρ ^ 2 ∈ T ⊓ I
  obs_a : ∀ X : Subgroup G, X ≤ T ⊓ I → X ≠ ⊥ → I ≤ Subgroup.normalizer (X : Set G) →
    IsIStar T M u (Subgroup.normalizer (X : Set G)) ∧
      T ⊓ Subgroup.normalizer (X : Set G) = T ⊓ I ∧
      IsSylowTwoOf (T ⊓ I) (Subgroup.normalizer (X : Set G))

structure Facts1469A5 (T M : Subgroup G) (u : G) (I K₁ K₂ : Subgroup G) : Prop where
  c : pCoreOf 2 (mcOf T) ≤ pCoreOf 2 (I ⊓ mcOf T)
  d : T ⊓ I = tZero T u
  e : omegaOneCenterOf (pCoreOf 2 (I ⊓ mcOf T)) ≤ omegaOneCenterOf (pCoreOf 2 (mcOf T))
  f : oTwoUpper (oTwoFstarIn (mcOf T)) ≤ Subgroup.centralizer
        ((omegaOneCenterOf (pCoreOf 2 (mcOf T)) ⊔ omegaOneCenterOf (pCoreOf 2 (I ⊓ mcOf T)) :
          Subgroup G) : Set G)
  g1 : IsElemAbelian 2 (dOf1469 T I K₁ K₂)
  g2 : pCoreOf 2 I = dOf1469 T I K₁ K₂ ⊔ pCoreOf 2 (K₁ ⊔ K₂)
  g3 : omegaOneCenterOf (pCoreOf 2 (I ⊓ mcOf T)) =
    dOf1469 T I K₁ K₂ ⊔ z0Of1469 (I ⊓ mcOf T) K₁ K₂

@[expose] def Input1469C126 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I S Iz : Subgroup G),
    IsSQTKTC I → CharTwo I → MinParabolic I S Iz → cgsIn I S ≤ Iz →
    ∃ (r : ℕ) (K : Fin r → Subgroup G), IsBlockProduct I S r K ∧ ∀ i, ¬ K i ≤ Iz

@[expose] def Input1469Lin2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I S Iz : Subgroup G) (z : G) (r : ℕ) (K : Fin r → Subgroup G),
    IsSQTKTC I → CharTwo I → MinParabolic I S Iz → IsBlockProduct I S r K →
    z ∈ quasithinOmegaOneCenter S → z ≠ 1 → Iz = I ⊓ Subgroup.centralizer ({z} : Set G) →
    (∀ i, ¬ K i ≤ Iz) →
    (∃ i, ∃ n : ℕ, 1 < n ∧ IsLin2Type (K i) n) → centerOf Iz ≤ centerOf I

@[expose] def Input1469C61 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I S Iz : Subgroup G) (r : ℕ) (K : Fin r → Subgroup G) (ρ : G),
    IsSQTKTC I → CharTwo I → MinParabolic I S Iz → IsBlockProduct I S r K →
    (∀ i, ¬ K i ≤ Iz) → (∀ i, IsAltType (K i) 3 ∨ IsAltType (K i) 5) →
    ¬ (r = 2 ∧ ∀ i, IsAltType (K i) 5) →
    ρ ∈ Subgroup.normalizer (S : Set G) → ρ ∉ S → ρ ^ 2 ∈ S →
    (∀ X : Subgroup G, X ≤ S → X ≠ ⊥ → I ≤ Subgroup.normalizer (X : Set G) →
      (S ⊔ Subgroup.zpowers ρ) ⊓ Subgroup.normalizer (X : Set G) ≤ S) →
    Nat.card S ≤ 2 ^ 9

@[expose] def Input1469A5J : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I S Iz K₁ K₂ : Subgroup G),
    IsSQTKTC I → CharTwo I → MinParabolic I S Iz → IsBlockProduct I S 2 ![K₁, K₂] →
    IsAltType K₁ 5 → IsAltType K₂ 5 → ¬ K₁ ≤ Iz →
    thompsonJ (pCoreOf 2 Iz) = thompsonJ (pCoreOf 2 I)

@[expose] def Input1469A5C567 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I S Iz K₁ K₂ Λ : Subgroup G),
    IsSQTKTC I → CharTwo I → MinParabolic I S Iz → IsBlockProduct I S 2 ![K₁, K₂] →
    IsAltType K₁ 5 → IsAltType K₂ 5 → ¬ K₁ ≤ Iz →
    HypC51 I Λ S S → S.relIndex Λ = 2 →
    (∀ R₀ : Subgroup G, R₀ ≤ S → R₀ ≠ ⊥ → ¬ (Λ ⊔ I ≤ Subgroup.normalizer (R₀ : Set G))) →
    IsElemAbelian 2 (S ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G)) ∧
      S ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) ≤ centerOf (baum S) ∧
      pCoreOf 2 I = (S ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G)) ⊔
        pCoreOf 2 (K₁ ⊔ K₂) ∧
      omegaOneCenterOf (pCoreOf 2 Iz) =
        (S ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G)) ⊔ z0Of1469 Iz K₁ K₂

@[expose] def Input1469A5DOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I K₁ K₂ : Subgroup G) (ρ : G),
    Ctx1469A5 T M H u I K₁ K₂ ρ → Facts1469A5 T M u I K₁ K₂ → dOf1469 T I K₁ K₂ ≠ ⊥ →
    yOfL22 T M ⊔ T =
      (lD1469 T M (dOf1469 T I K₁ K₂) ⊔ (T ⊓ I)) ⊔ pCoreOf 2 (yOfL22 T M ⊔ T) →
      T ⊓ Subgroup.centralizer (yOfL22 T M : Set G) ≠ ⊥

@[expose] def Input1469A5DTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I K₁ K₂ : Subgroup G) (ρ : G),
    Ctx1469A5 T M H u I K₁ K₂ ρ → Facts1469A5 T M u I K₁ K₂ → dOf1469 T I K₁ K₂ ≠ ⊥ →
    ¬ (yOfL22 T M ⊔ T =
      (lD1469 T M (dOf1469 T I K₁ K₂) ⊔ (T ⊓ I)) ⊔ pCoreOf 2 (yOfL22 T M ⊔ T)) → False

@[expose] def Input1469A5Fin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I K₁ K₂ : Subgroup G) (ρ : G),
    Ctx1469A5 T M H u I K₁ K₂ ρ → Facts1469A5 T M u I K₁ K₂ → dOf1469 T I K₁ K₂ = ⊥ → False

@[expose] def Shape1469B (S Iz K I : Subgroup G) : Prop :=
  (∃ p : ℕ, IsFermatOrMersennePrime p ∧ 7 < p ∧ IsPSL 2 p 1 ↥(E2.star Iz I K)) ∨
  ((IsPSL 3 2 1 ↥(E2.star Iz I K) ∨ IsAlt 6 ↥(E2.star Iz I K)) ∧
    E2.IsDiagramNontrivial (E2.star Iz I S) (E2.star Iz I K) (E2.star Iz I (S ⊓ K))) ∨
  IsPSL 3 3 1 ↥(E2.star Iz I K)

@[expose] def Input1469B1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I S Iz : Subgroup G) (z : G),
    IsSQTKTC I → ¬ CharTwo I → MinParabolic I S Iz →
    z ∈ quasithinOmegaOneCenter S → z ≠ 1 → Iz = I ⊓ Subgroup.centralizer ({z} : Set G) →
    (∃ L : Subgroup G, IsComponentIn L I) →
    (∀ L : Subgroup G, IsComponentIn L I → ⁅L, Subgroup.zpowers z⁆ = L ∧ Lemma115Cases L z) →
    (∃ K : Subgroup G, K ∈ cComp I ∧ I = K ⊔ S ∧
      CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) ∧ E2.E22Cases I S Iz K) →
    ∃ K : Subgroup G, K ∈ cComp I ∧ I = K ⊔ S ∧
      CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) ∧ E2.E22Cases I S Iz K ∧
      Shape1469B S Iz K I

@[expose] def Input1469B2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I S Iz K : Subgroup G),
    IsSQTKTC I → ¬ CharTwo I → MinParabolic I S Iz → K ∈ cComp I → I = K ⊔ S →
    CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) → E2.E22Cases I S Iz K →
    Shape1469B S Iz K I →
    ∀ A : Subgroup G, A ≤ S → S ≤ Subgroup.normalizer (A : Set G) → IsElemAbelian 2 A →
      4 ≤ mIdx A (pCoreOf 2 I) → False

@[expose] def i1Of1469 (T M I : Subgroup G) : Subgroup G := lI T M I ⊔ (T ⊓ I)

@[expose] def wOf1469 (K : Subgroup G) : Subgroup G := ⁅omegaOneCenterOf (pCoreOf 2 K), K⁆

structure Hyp14610 (T M H : Subgroup G) (u : G) (I I₂ : Subgroup G) : Prop where
  setting : Setting146 G T M
  hH : IsHTM T M H
  hu : IsInvU T M H u
  hI : IsIStar T M u I
  hT : 2 ^ 11 < Nat.card T
  hrank : 4 ≤ mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G))
  le_I₂ : T ⊓ I ≤ I₂
  I₂_le : I₂ ≤ H
  s3 : Nonempty (OTwoQuot I₂ ≃* Equiv.Perm (Fin 3))
  gen : I = i1Of1469 T M I ⊔ I₂
  cent : T ⊓ I = tU T u → I ≤ Subgroup.centralizer ({u} : Set G)

structure Facts14610 (T M H : Subgroup G) (u : G) (I I₂ : Subgroup G) : Prop
    extends Hyp14610 T M H u I I₂ where
  c1 : CGS (pCoreOf 2 (i1Of1469 T M I)) ≤ M
  c2 : pCoreOf 2 (i1Of1469 T M I) ≠ pCoreOf 2 I₂
  c3 : ∀ P : Subgroup G, P ≤ I → i1Of1469 T M I ≤ Subgroup.normalizer (P : Set G) →
    lI T M I ≤ P ∨ P ≤ M ⊓ Subgroup.centralizer (VZ T M : Set G)
  c4 : CharTwo I

@[expose] def Input14610Four : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ : Subgroup D) (z : D) (A : Subgroup D),
    IsGoldschmidtTriple G₁ G₂ → F6.F618ConclusionCat G₁ G₂ →
    z ≠ 1 → z ^ 2 = 1 → z ∈ G₁ ⊓ G₂ → (∀ t ∈ G₁ ⊓ G₂, t * z = z * t) →
    G₂ ≤ Subgroup.centralizer ({z} : Set D) →
    A ≤ G₂ → IsElemAbelian 2 A → G₂ ≤ Subgroup.normalizer (A : Set D) →
    2 ^ 4 ≤ Nat.card A → False

structure Concl14610List (T M : Subgroup G) (I I₂ K : Subgroup G) : Prop where
  le : K ≤ I
  normal : I ≤ Subgroup.normalizer (K : Set G)
  eq_residual : K = oTwoUpper I
  eq_sup : I = K ⊔ (T ⊓ I)
  gen : K = oTwoUpper (i1Of1469 T M I) ⊔ oTwoUpper I₂
  shape : (IsPSL 3 2 1 (OTwoQuot K) ∧ True) ∨
    (IsBlock2 I K ∧
      ((IsHatA6Block K ∧ True) ∨ (IsG2Block K ∧ True) ∨
       (IsAlt 6 (OTwoQuot K) ∧ True ∧
         (Nat.card (wOf1469 K) = 2 ^ 4 ∨ Nat.card (wOf1469 K) = 2 ^ 5)) ∨
       (IsAlt 7 (OTwoQuot K) ∧ True ∧
         (Nat.card (wOf1469 K) = 2 ^ 4 ∨ Nat.card (wOf1469 K) = 2 ^ 6))))
  v_le_w : VZ T M ≤ wOf1469 K

@[expose] def Input14610List : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I I₂ : Subgroup G),
    ASC27Statement G → Facts14610 T M H u I I₂ →
    F6.IsGoldschmidtTripleIn I (i1Of1469 T M I) I₂ →
    F6.F618ConclusionCat
      (((i1Of1469 T M I).subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
      ((I₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) →
    ∃ K : Subgroup G, Concl14610List T M I I₂ K

@[expose] def Input14610L32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I I₂ K : Subgroup G),
    Facts14610 T M H u I I₂ → Concl14610List T M I I₂ K →
    IsPSL 3 2 1 (OTwoQuot K) → Nat.card (conjClosure (VZ T M) I₂) = 2 ^ 3

@[expose] def Input14610Hat6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G),
    IsHatA6Block K →
      wOf1469 K ⊓ Subgroup.centralizer ((oTwoUpper (oTwoZIn K) : Subgroup G) : Set G) = ⊥

@[expose] def Input14610G22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I I₂ K : Subgroup G),
    Facts14610 T M H u I I₂ → Concl14610List T M I I₂ K →
    IsG2Block K → Nat.card (conjClosure (VZ T M) I₂) = 2 ^ 3

@[expose] def Input14610Rank4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I I₂ K : Subgroup G),
    Facts14610 T M H u I I₂ → Concl14610List T M I I₂ K →
    (IsAlt 6 (OTwoQuot K) ∨ IsAlt 7 (OTwoQuot K)) → Nat.card (wOf1469 K) = 2 ^ 4 →
    Nat.card (conjClosure (VZ T M) I₂) = 2 ^ 3

@[expose] def Input14610PermFixed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I I₂ K : Subgroup G),
    Facts14610 T M H u I I₂ → Concl14610List T M I I₂ K →
    ((IsAlt 6 (OTwoQuot K) ∧ Nat.card (wOf1469 K) = 2 ^ 5) ∨
      (IsAlt 7 (OTwoQuot K) ∧ Nat.card (wOf1469 K) = 2 ^ 6)) →
    wOf1469 K ⊓ Subgroup.centralizer ((lI T M I : Subgroup G) : Set G) ≠ ⊥

@[expose] def Input14610PermTu : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I I₂ K : Subgroup G),
    Facts14610 T M H u I I₂ → Concl14610List T M I I₂ K →
    ((IsAlt 6 (OTwoQuot K) ∧ Nat.card (wOf1469 K) = 2 ^ 5) ∨
      (IsAlt 7 (OTwoQuot K) ∧ Nat.card (wOf1469 K) = 2 ^ 6)) →
    T ⊓ I = tU T u → Nat.card (conjClosure (VZ T M) I₂) ≠ 2 ^ 3 → False

end CFSG.Quasithin
