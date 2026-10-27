module

public import CFSG.RankThree.PartOne.HNB.Transport
public import CFSG.RankThree.PartOne.HNB.InnerAction
import CFSG.RankThree.GroupTheory.SteinbergBMVanishingFullPerfectSupplement

public section

namespace CFSG.RankThree.PartOne.HNB

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open CFSG.Assembly (InCatalog)
open scoped Pointwise commutatorElement

abbrev BridgeHyp : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
    (∃ a b : S, a * b ≠ b * a) → InCatalog S → CFSG.Blueprint.Catalog S

namespace Successor

variable {G : Type} [Group G] {A L : Subgroup G} {a : Actor G A L} (s : Successor a)

abbrev NX : Subgroup a.H := Subgroup.normalizer (s.X : Set a.H)

abbrev RN : Subgroup s.NX := a.RH.subgroupOf s.NX

@[expose] def bar (S : Subgroup a.H) : Subgroup (↥s.X ⧸ Subgroup.center ↥s.X) :=
  (S.subgroupOf s.X).map (QuotientGroup.mk' (Subgroup.center ↥s.X))

@[expose] noncomputable def Phi : ↥s.NX →* MulAut (↥s.X ⧸ Subgroup.center ↥s.X) :=
  centerQuotientConj s.X

theorem Phi_eq_conj {n : s.NX} {x : s.X} (hn : s.X.normalizerMonoidHom n = MulAut.conj x) :
    s.Phi n = MulAut.conj (x : ↥s.X ⧸ Subgroup.center ↥s.X) := by
  apply MulEquiv.ext
  intro v
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥s.X) v
  show ((s.X.normalizerMonoidHom n l : s.X) : ↥s.X ⧸ Subgroup.center ↥s.X) = _
  rw [hn, MulAut.conj_apply]
  rfl

theorem normalizerMonoidHom_of_mem (x : s.X) :
    s.X.normalizerMonoidHom ⟨(x : a.H), Subgroup.le_normalizer x.2⟩ = MulAut.conj x := by
  apply MulEquiv.ext
  intro l
  apply Subtype.ext
  exact coe_normalizerMonoidHom_apply _ _

theorem Phi_of_mem (x : s.X) :
    s.Phi ⟨(x : a.H), Subgroup.le_normalizer x.2⟩ =
      MulAut.conj (x : ↥s.X ⧸ Subgroup.center ↥s.X) :=
  s.Phi_eq_conj (s.normalizerMonoidHom_of_mem x)

theorem mem_RN_iff {n : s.NX} : n ∈ s.RN ↔ (((n : a.H)) : G) ∈ a.R := Iff.rfl

theorem mem_normalizer_RN {n : s.NX}
    (hn : ((n : a.H) : G) ∈ Subgroup.normalizer (a.R : Set G)) :
    n ∈ Subgroup.normalizer (s.RN : Set s.NX) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [s.mem_RN_iff, s.mem_RN_iff]
  exact Subgroup.mem_normalizer_iff.mp hn ((g : a.H) : G)

theorem isPGroup_RN : IsPGroup 2 s.RN := (a.R_isPGroup.comap_subtype).comap_subtype

@[expose] def cN [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) : s.NX :=
  ⟨a.cH, s.A0_le_normalizer h a.cH_mem_A0H⟩

theorem orderOf_cN [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) : orderOf (s.cN h) = 5 := by
  rw [cN, Subgroup.orderOf_mk, a.orderOf_cH]

theorem cN_pow [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) : s.cN h ^ 5 = 1 := by
  have := pow_orderOf_eq_one (s.cN h)
  rwa [s.orderOf_cN h] at this

theorem RN_map_eq [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) :
    s.RN.map (a.H.subtype.comp s.NX.subtype) = a.R := by
  rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le (s.R_le_normalizer h),
    Subgroup.map_subgroupOf_eq_of_le a.R_le_H]

theorem commutator_RN [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) :
    ⁅s.RN, Subgroup.zpowers (s.cN h)⁆ = s.RN := by
  have hinj : Function.Injective (a.H.subtype.comp s.NX.subtype) :=
    a.H.subtype_injective.comp s.NX.subtype_injective
  apply Subgroup.map_injective hinj
  rw [Subgroup.map_commutator, s.RN_map_eq h, MonoidHom.map_zpowers]
  exact a.R_commutator_self

theorem catalog [Finite G] (hbridge : BridgeHyp) (hK : CatalogPrimeTwoAutomorphismsInner)
    (h : SteinbergBM.SectionTenSetup G 5 A) :
    CFSG.Blueprint.Catalog (↥s.X ⧸ Subgroup.center ↥s.X) := by
  have hq := s.isQuasisimple_X hbridge hK h
  have : IsSimpleGroup (↥s.X ⧸ Subgroup.center ↥s.X) := hq.2.1
  exact hbridge _ hq.2.2 (a.isKGroup_H h s.X (Subgroup.center ↥s.X) this)

theorem center_V [Finite G] (hbridge : BridgeHyp) (hK : CatalogPrimeTwoAutomorphismsInner)
    (h : SteinbergBM.SectionTenSetup G 5 A) :
    Subgroup.center (↥s.X ⧸ Subgroup.center ↥s.X) = ⊥ := by
  have hq := s.isQuasisimple_X hbridge hK h
  have : IsSimpleGroup (↥s.X ⧸ Subgroup.center ↥s.X) := hq.2.1
  exact SteinbergBM.center_eq_bot_of_isSimpleGroup hq.2.2

theorem inner_of_RN [Finite G] (hbridge : BridgeHyp) (hK : CatalogPrimeTwoAutomorphismsInner)
    (h : SteinbergBM.SectionTenSetup G 5 A) :
    ∀ r ∈ s.RN, s.Phi r ∈
      (MulAut.conj : (↥s.X ⧸ Subgroup.center ↥s.X) →*
        MulAut (↥s.X ⧸ Subgroup.center ↥s.X)).range := by
  intro r hr
  have hq := s.isQuasisimple_X hbridge hK h
  have hcat := s.catalog hbridge hK h
  have hc : s.cN h ∈ Subgroup.normalizer (s.RN : Set s.NX) :=
    s.mem_normalizer_RN (n := s.cN h) a.c_mem_normalizer_R
  have hP : IsPGroup 5 ((Subgroup.zpowers (s.cN h)).map s.X.normalizerMonoidHom) :=
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, s.orderOf_cN h]; norm_num)).map _
  have hQ : IsPGroup 2 (s.RN.map s.X.normalizerMonoidHom) := s.isPGroup_RN.map _
  have hPQ : (Subgroup.zpowers (s.cN h)).map s.X.normalizerMonoidHom ≤
      Subgroup.normalizer ((s.RN.map s.X.normalizerMonoidHom : Subgroup (MulAut ↥s.X)) :
        Set (MulAut ↥s.X)) :=
    (Subgroup.map_mono (Subgroup.zpowers_le.mpr hc)).trans (Subgroup.le_normalizer_map _)
  have hcomm : ⁅s.RN.map s.X.normalizerMonoidHom,
      (Subgroup.zpowers (s.cN h)).map s.X.normalizerMonoidHom⁆ =
        s.RN.map s.X.normalizerMonoidHom := by
    rw [← Subgroup.map_commutator, s.commutator_RN h]
  obtain ⟨x, hx⟩ := hK ↥s.X hq hcat 5 _ _ (by norm_num) (by norm_num) hP hQ hPQ hcomm
    (Subgroup.mem_map_of_mem _ hr)
  exact ⟨(x : ↥s.X ⧸ Subgroup.center ↥s.X), (s.Phi_eq_conj hx.symm).symm⟩

theorem isPGroup_U [Finite G] (hbridge : BridgeHyp) (hK : CatalogPrimeTwoAutomorphismsInner)
    (h : SteinbergBM.SectionTenSetup G 5 A) : IsPGroup 2 (innerPart s.Phi s.RN) :=
  isPGroup_innerPart (s.center_V hbridge hK h) s.isPGroup_RN

theorem U_ne_bot [Finite G] (hbridge : BridgeHyp) (hK : CatalogPrimeTwoAutomorphismsInner)
    (h : SteinbergBM.SectionTenSetup G 5 A) : innerPart s.Phi s.RN ≠ ⊥ := by
  intro hbot
  have hq := s.isQuasisimple_X hbridge hK h
  have : Group.IsPerfect s.X := hq.1
  obtain ⟨k, hk, r, hr, hmove⟩ := a.exists_move h
  have hrH : r ∈ a.H := a.R_le_H hr
  have hrRH : (⟨r, hrH⟩ : a.H) ∈ a.RH := Subgroup.mem_subgroupOf.mpr hr
  have hnR : (⟨⟨r, hrH⟩, s.R_le_normalizer h hrRH⟩ : s.NX) ∈ s.RN := (s.mem_RN_iff).mpr hr
  obtain ⟨u, hu, hconj⟩ := exists_mem_innerPart (s.inner_of_RN hbridge hK h) hnR
  rw [hbot, Subgroup.mem_bot] at hu
  have hΦ : s.Phi ⟨⟨r, hrH⟩, s.R_le_normalizer h hrRH⟩ = 1 := by
    rw [← hconj, hu, map_one]
  have hcomm := commute_of_centerQuotientAction_eq_one (s.R_le_normalizer h)
    (⟨⟨r, hrH⟩, hrRH⟩ : a.RH) hΦ ⟨⟨k, a.K_le_H hk⟩, s.hKX (Subgroup.mem_subgroupOf.mpr hk)⟩
  have hcomm' : r * k = k * r := congrArg (fun z : a.H => (z : G)) hcomm
  apply hmove
  have : r * k * r⁻¹ * k⁻¹ = 1 := by
    rw [hcomm']
    group
  rw [this]
  exact Subgroup.one_mem _

theorem beta_mem_U [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) {u : ↥s.X ⧸ Subgroup.center ↥s.X}
    (hu : u ∈ innerPart s.Phi s.RN) : s.beta h u ∈ innerPart s.Phi s.RN := by
  have hc : s.cN h ∈ Subgroup.normalizer (s.RN : Set s.NX) :=
    s.mem_normalizer_RN (n := s.cN h) a.c_mem_normalizer_R
  exact Φ_mem_innerPart hc hu

theorem Y_conj_mem_U {y u : ↥s.X ⧸ Subgroup.center ↥s.X} (hy : y ∈ s.bar a.YH)
    (hu : u ∈ innerPart s.Phi s.RN) : y * u * y⁻¹ ∈ innerPart s.Phi s.RN := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hxY : ((x : a.H) : G) ∈ a.Y := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hx)
  have hn : (⟨(x : a.H), Subgroup.le_normalizer x.2⟩ : s.NX) ∈
      Subgroup.normalizer (s.RN : Set s.NX) :=
    s.mem_normalizer_RN (a.Y_le_normalizer_R hxY)
  exact conj_mem_innerPart hn (s.Phi_of_mem x).symm hu

theorem closure_U [Finite G] (hbridge : BridgeHyp) (hK : CatalogPrimeTwoAutomorphismsInner)
    (h : SteinbergBM.SectionTenSetup G 5 A) :
    Subgroup.closure {x | ∃ u ∈ innerPart s.Phi s.RN, x = u⁻¹ * s.beta h u} =
      innerPart s.Phi s.RN :=
  closure_eq_innerPart (s.center_V hbridge hK h) (s.inner_of_RN hbridge hK h)
    (s.mem_normalizer_RN (n := s.cN h) a.c_mem_normalizer_R) (s.cN_pow h) (s.commutator_RN h)

end Successor

end CFSG.RankThree.PartOne.HNB
