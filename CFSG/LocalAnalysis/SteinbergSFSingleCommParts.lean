module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixG
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Objects

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  (φ : L ≃* antiSp K) (t : G)

abbrev U (k : Axis) : Subgroup G := pull φ (rootU K k)

abbrev A (k : Axis) : Subgroup G := pull φ (rootA K k)

abbrev P : Subgroup G := pull φ (antiUnipotent K)

abbrev Z₀ : Subgroup G := pull φ (antiUnipotentCenter K)

abbrev J₀ : Subgroup G := pull φ (diagTorus K)

abbrev J (k : Axis) : Subgroup G := pull φ (FullCenterTorus.axisTorus K k)

abbrev Q : Subgroup G := P φ ⊔ zpowers t

abbrev D (k : Axis) : Subgroup G :=
  (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootU K k) : Subgroup G) : Set G))).map
    (normalizer ((zpowers t ⊔ pull φ (rootU K k) : Subgroup G) : Set G)).subtype

abbrev E (k : Axis) : Subgroup G :=
  (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K k) : Subgroup G) : Set G))).map
    (normalizer ((zpowers t ⊔ pull φ (rootA K k) : Subgroup G) : Set G)).subtype

abbrev E₀ : Subgroup G := E φ t Axis.one ⊓ E φ t Axis.two

abbrev F : Subgroup G :=
  closure {x : G | ∃ e ∈ E₀ φ t, ∃ j ∈ pull φ (diagTorus K), x = e⁻¹ * (j⁻¹ * e * j)}

abbrev Kc (k : Axis) : Subgroup G := A φ k ⊔ (F φ t ⊓ D φ t k)

abbrev Kstar : Subgroup G := Kc φ t Axis.one ⊔ Kc φ t Axis.two

abbrev w (k : Axis) : G := ((φ.symm (FullCenterWeyl.weylElt K k) : L) : G)

abbrev R (k : Axis) : Subgroup G := P φ ⊔ zpowers t ⊔ E φ t k

abbrev P₁ (i : Axis) : Subgroup G :=
  (CFSG.pCore 2 (normalizer ((D φ t i : Subgroup G) : Set G))).map
    (normalizer ((D φ t i : Subgroup G) : Set G)).subtype

abbrev En (k : Axis) : Subgroup G :=
  normalizer ((E φ t k : Subgroup G) : Set G) ⊓ normalizer ((Kc φ t k : Subgroup G) : Set G)

abbrev P₂ (k : Axis) : Subgroup G := (CFSG.pCore 2 (En φ t k)).map (En φ t k).subtype

abbrev T₁ (i : Axis) : Subgroup G := R φ t i ⊔ P₁ φ t i

abbrev T₀ (j : Axis) : Subgroup G := R φ t j ⊔ P₂ φ t j

abbrev T₂ (j : Axis) : Subgroup G := T₀ φ t j ⊓ normalizer (R φ t j : Set G)

abbrev Tbar (i : Axis) : Subgroup G := T₁ φ t i ⊔ T₂ φ t i.swap

abbrev P₀ (i : Axis) : Subgroup G := P₁ φ t i ⊓ P₂ φ t i.swap

abbrev Mc (i : Axis) : Subgroup G :=
  closure {x : G | ∃ p ∈ P₀ φ t i, ∃ j ∈ pull φ (diagTorus K), x = p⁻¹ * (j⁻¹ * p * j)}

abbrev Tplus (i : Axis) : Subgroup G := Tbar φ t i ⊔ T₀ φ t i.swap

abbrev Mw (i k : Axis) : Subgroup G :=
  (Mc φ t i).map (MulAut.conj (w φ k)⁻¹).toMonoidHom

abbrev Mhat (i k : Axis) : Subgroup G := Mc φ t i ⊔ Mw φ t i k

abbrev S (i : Axis) : Subgroup G := Mhat φ t i Axis.one ⊔ Mhat φ t i Axis.two

abbrev Dstar (i : Axis) : Subgroup G := Mhat φ t i i ⊔ Kc φ t i.swap

abbrev Fw (k : Axis) : Subgroup G := (F φ t).map (MulAut.conj (w φ k)⁻¹).toMonoidHom

abbrev Xk (k : Axis) : Subgroup G := F φ t ⊔ Fw φ t k

abbrev Wk (k : Axis) : Subgroup G := F φ t ⊓ centralizer (J φ k : Set G)

abbrev Bstar (i : Axis) : Subgroup G := Mc φ t i ⊔ Kstar φ t

abbrev Cstar (i : Axis) : Subgroup G := Mc φ t i ⊔ Fw φ t i.swap

abbrev Astar (i : Axis) : Subgroup G := Mc φ t i ⊔ Kstar φ t ⊔ Fw φ t i.swap

abbrev Sk (k : Axis) : Subgroup G :=
  ⁅L ⊓ centralizer (J φ k : Set G), L ⊓ centralizer (J φ k : Set G)⁆

abbrev Vtor (i k : Axis) : Subgroup G := Mc φ t i ⊓ centralizer (J φ k : Set G)

abbrev Ytor (k : Axis) : Subgroup G :=
  closure {x : G | ∃ g ∈ centralizer (J φ k : Set G), ∃ s ∈ Sk φ k, x = g⁻¹ * s * g}

abbrev Ytilde (k : Axis) : Subgroup G :=
  (Ytor φ k).map (MulAut.conj (w φ k.swap)⁻¹).toMonoidHom

end Objects

structure SCSetting {G : Type} [Group G] (L : Subgroup G) (K : Type) [Field K] [CharP K 2] (n : ℕ)
    (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop where
  kproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  oddCore : CFSG.Open.standardComponentOddCore G = ⊥
  standard : CFSG.Open.standardComponentIsStandard L
  not_normal : ¬ L.Normal
  oddCore_centralizer : CFSG.Open.standardComponentOddCore (centralizer ({t} : Set G)) = ⊥
  fc : FullCenter.FCHyp L K n φ t
  ne_bot : ⁅A φ i, F φ t ⊓ D φ t i.swap⁆ ≠ ⊥
  eq_bot : ⁅A φ i.swap, F φ t ⊓ D φ t i⁆ = ⊥

structure SixHConclusion {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
    (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop where
  sq_Mhat_i : closure {x : G | ∃ y ∈ Mhat φ t i i, x = y * y} = U φ i
  center_Mhat_i : (center ↥(Mhat φ t i i)).map (Mhat φ t i i).subtype = U φ i
  sq_Mhat_j : closure {x : G | ∃ y ∈ Mhat φ t i i.swap, x = y * y} = Kc φ t i.swap
  center_Mhat_j : (center ↥(Mhat φ t i i.swap)).map (Mhat φ t i i.swap).subtype = Kc φ t i.swap
  normal_Mhat : ∀ k : Axis, SixG.MNNormalIn (Mhat φ t i k) (Tplus φ t i) (J₀ φ)
  normal_M : SixG.MNNormalIn (Mc φ t i) (Tplus φ t i) (J₀ φ)
  normal_Dstar : SixG.MNNormalIn (Dstar φ t i) (Tplus φ t i) (J₀ φ)
  center_Dstar : (center ↥(Dstar φ t i)).map (Dstar φ t i).subtype = U φ i
  card_Dstar : Nat.card (Dstar φ t i) = Nat.card K ^ 8
  inf_M_K : Mc φ t i ⊓ Kc φ t i.swap = F φ t ⊓ D φ t i.swap
  maximal_Dstar : ∃ _ : ((U φ i).subgroupOf (Dstar φ t i)).Normal,
    SixG.MNMaximal (Dstar φ t i) (Mhat φ t i i) (Mc φ t i ⊔ Kc φ t i.swap) (Dstar φ t i)
      (U φ i)
  maximal_P₁ : ∃ _ : ((U φ i).subgroupOf (P₁ φ t i)).Normal,
    SixG.MNMaximal (P₁ φ t i) (Mhat φ t i i) (D φ t i) (P₁ φ t i) (U φ i)
  inf_Mhat : Mhat φ t i Axis.one ⊓ Mhat φ t i Axis.two = Mc φ t i
  card_S : Nat.card (S φ t i) = Nat.card K ^ 10
  sup_t : S φ t i ⊔ zpowers t = Tplus φ t i
  inf_t : S φ t i ⊓ zpowers t = ⊥
  center_Tplus : (center ↥(Tplus φ t i)).map (Tplus φ t i).subtype = U φ i
  isPGroup_Tplus : IsPGroup 2 ↥(Tplus φ t i)

@[expose] def SixHStatement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
    [Finite K] [CharP K 2] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis},
    SCSetting L K n φ t i → SixHConclusion φ t i

structure EmbConclusion {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
    (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop where
  Ytilde_le : Ytilde φ i ≤ normalizer (Mhat φ t i i : Set G)
  Vw_le_Ytilde : (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom ≤ Ytilde φ i
  inf_Vw : Mhat φ t i i ⊓ (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom = ⊥
  sup_Vw : Mhat φ t i i ⊔ (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom = S φ t i

@[expose] def EmbStatement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
    [Finite K] [CharP K 2] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis},
    SCSetting L K n φ t i → SixHConclusion φ t i → EmbConclusion φ t i

structure SixKConclusion {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
    (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop where
  slice : ∀ g : G, g⁻¹ * t * g ∈ Tplus φ t i → ∃ s ∈ S φ t i, g⁻¹ * t * g = s⁻¹ * t * s
  centralizer_S : S φ t i ⊓ centralizer ({t} : Set G) = P φ
  centralizer_Tplus : Tplus φ t i ⊓ centralizer ({t} : Set G) = P φ ⊔ zpowers t

@[expose] def SixKStatement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
    [Finite K] [CharP K 2] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis},
    SCSetting L K n φ t i → SixHConclusion φ t i → EmbConclusion φ t i →
      SixKConclusion φ t i

structure FieldFusionConclusion {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
    [CharP K 2] (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop where
  normalizer_le : normalizer (Tplus φ t i : Set G) ≤ normalizer (S φ t i : Set G)
  slice : ∀ g : G, g⁻¹ * t * g ∈ normalizer (Tplus φ t i : Set G) →
    ∃ s ∈ S φ t i, g⁻¹ * t * g = s⁻¹ * t * s

@[expose] def FieldFusionStatement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
    [Finite K] [CharP K 2] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis},
    SCSetting L K n φ t i → SixHConclusion φ t i → EmbConclusion φ t i → SixKConclusion φ t i →
      FieldFusionConclusion φ t i

@[expose] def CanonicityConclusion {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
    [CharP K 2] (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  centralizer ({t} : Set G) ⊓ normalizer ((P φ ⊔ zpowers t : Subgroup G) : Set G) ≤
    normalizer (Tplus φ t i : Set G)

@[expose] def CanonicityStatement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
    [Finite K] [CharP K 2] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis},
    SCSetting L K n φ t i → CanonicityConclusion φ t i

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
