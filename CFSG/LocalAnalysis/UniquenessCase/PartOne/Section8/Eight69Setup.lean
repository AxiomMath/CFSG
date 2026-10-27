module

public import CFSG.GroupTheory.PCore.InfPCoreOf
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open scoped commutatorElement

private lemma subgroupOf_sup_pCore_eq_top {G : Type} [Group G]
    (L X : Subgroup G) (hXL : X ≤ L)
    (hsup : X ⊔ CFSG.Open.pCoreOf 2 L = L) :
    X.subgroupOf L ⊔ CFSG.pCore 2 ↥L = ⊤ := by
  rw [← Subgroup.map_subtype_inj (H := L)]
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hXL, Subgroup.map_top,
    Subgroup.range_subtype]
  simpa [CFSG.Open.pCoreOf] using hsup

private lemma surjective_inclusion_comp_pCore_mk {G : Type} [Group G]
    (L X : Subgroup G) (hXL : X ≤ L)
    (hsup : X ⊔ CFSG.Open.pCoreOf 2 L = L) :
    Function.Surjective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hXL)) := by
  have hO_le_L : CFSG.Open.pCoreOf 2 L ≤ L := Subgroup.map_subtype_le _
  have hsup_l : X.subgroupOf L ⊔ (CFSG.Open.pCoreOf 2 L).subgroupOf L = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hXL hO_le_L, hsup, Subgroup.subgroupOf_self]
  haveI : ((CFSG.Open.pCoreOf 2 L).subgroupOf L).Normal := by
    have h : (CFSG.Open.pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
      change (CFSG.Open.pCoreOf 2 L).comap L.subtype = CFSG.pCore 2 ↥L
      rw [CFSG.Open.pCoreOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
    rw [h]
    infer_instance
  intro y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  have hl : l ∈ X.subgroupOf L ⊔ (CFSG.Open.pCoreOf 2 L).subgroupOf L := by
    rw [hsup_l]
    exact Subgroup.mem_top l
  obtain ⟨yl, hyl, zl, hzl, hlyz⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := X.subgroupOf L)
      (t := (CFSG.Open.pCoreOf 2 L).subgroupOf L)).mp hl
  obtain ⟨n, hn, hnz⟩ := Subgroup.mem_map.mp hzl
  have hzl1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) zl = 1 := by
    rw [show zl = n from (Subtype.ext hnz).symm]
    exact (MonoidHom.mem_ker).mp (by rwa [QuotientGroup.ker_mk'])
  have hylG : (yl : G) ∈ X := hyl
  refine ⟨⟨(yl : G), hylG⟩, ?_⟩
  have hyl_eq : (⟨(yl : G), hXL hylG⟩ : ↥L) = yl := Subtype.ext rfl
  show QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨(yl : G), hXL hylG⟩ : ↥L) =
    QuotientGroup.mk' (CFSG.pCore 2 ↥L) l
  rw [← hlyz, map_mul, hzl1, mul_one, hyl_eq]

private lemma ker_inclusion_comp_pCore_mk {G : Type} [Group G]
    (L X : Subgroup G) (hXL : X ≤ L) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hXL)).ker =
      (X ⊓ CFSG.Open.pCoreOf 2 L).subgroupOf X := by
  have hker_le :
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hXL)).ker ≤
        (CFSG.Open.pCoreOf 2 L).subgroupOf X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxN : (⟨x.1, hXL x.2⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      have hx' : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨x.1, hXL x.2⟩ : ↥L) = 1 := hx
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx'
    exact Subgroup.mem_map.mpr ⟨_, hxN, rfl⟩
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    exact ⟨x.2, hker_le (by rwa [MonoidHom.mem_ker])⟩
  · intro hx
    obtain ⟨n, hn, hno⟩ := Subgroup.mem_map.mp hx.2
    have hxN : (⟨x.1, hXL x.2⟩ : ↥L) = n := (Subtype.ext hno).symm
    show QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨x.1, hXL x.2⟩ : ↥L) = 1
    rw [hxN]
    exact (MonoidHom.mem_ker).mp (by rwa [QuotientGroup.ker_mk'])

theorem commutator_eq_self_of_minimal_supplement {G : Type} [Group G]
    (L X : Subgroup G) (hL : ⁅L, L⁆ = L) (hsup : X ⊔ CFSG.Open.pCoreOf 2 L = L)
    (hmin : ∀ X₀ : Subgroup G, X₀ < X → X₀ ⊔ CFSG.Open.pCoreOf 2 L ≠ L) :
    ⁅X, X⁆ = X := by
  have hXL : X ≤ L := by
    rw [← hsup]
    exact le_sup_left
  set Xl : Subgroup ↥L := X.subgroupOf L with hXl
  set Ol : Subgroup ↥L := CFSG.pCore 2 ↥L with hOl
  have hXl_map : Xl.map L.subtype = X := by
    rw [hXl, Subgroup.map_subgroupOf_eq_of_le hXL]
  have hOl_map : Ol.map L.subtype = CFSG.Open.pCoreOf 2 L := rfl
  have hsup_l : Xl ⊔ Ol = ⊤ := by
    simpa [Xl, Ol] using subgroupOf_sup_pCore_eq_top L X hXL hsup
  haveI : Ol.Normal := by
    rw [hOl]
    exact CFSG.pCore_normal (p := 2) (G := ↥L)
  let π : ↥L →* CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L :=
    QuotientGroup.mk' Ol
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Ol
  have hperf_l : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = (⊤ : Subgroup ↥L) := by
    rw [← Subgroup.map_subtype_inj (H := L), Subgroup.map_commutator, Subgroup.map_top,
      Subgroup.range_subtype, hL]
  have hperf_quot :
      ⁅(⊤ : Subgroup (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L)),
        (⊤ : Subgroup (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L))⁆ =
        (⊤ : Subgroup (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L)) := by
    have h := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥L)) (H₂ := ⊤) π
    rw [hperf_l, Subgroup.map_top_of_surjective π hπ] at h
    exact h.symm
  have hOmap : Ol.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hmapX : Xl.map π = ⊤ := by
    have h := congrArg (Subgroup.map π) hsup_l
    rw [Subgroup.map_sup, hOmap, sup_bot_eq, Subgroup.map_top_of_surjective π hπ] at h
    exact h
  have hmap_top_iff : ∀ A : Subgroup ↥L, A.map π = ⊤ ↔ A ⊔ Ol = ⊤ := by
    intro A
    constructor
    · intro h
      rw [eq_top_iff]
      intro x _
      have hmem : π x ∈ A.map π := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hmem
      have hxo : a⁻¹ * x ∈ Ol := by
        have h1 : QuotientGroup.mk' Ol (a⁻¹ * x) = 1 := by
          rw [map_mul, map_inv, hax, inv_mul_cancel]
        exact (QuotientGroup.eq_one_iff (a⁻¹ * x)).mp (by simpa using h1)
      rw [show x = a * (a⁻¹ * x) by group]
      exact Subgroup.mul_mem_sup ha hxo
    · intro h
      rw [eq_top_iff]
      intro y _
      obtain ⟨x, rfl⟩ := hπ y
      have hx : x ∈ A ⊔ Ol := by
        rw [h]
        exact Subgroup.mem_top x
      obtain ⟨a, ha, b, hb, hab⟩ :=
        (Subgroup.mem_sup_of_normal_right (s := A) (t := Ol)).mp hx
      have hb1 : π b = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
        exact hb
      have hx' : π x = π a := by
        rw [← hab, map_mul, hb1, mul_one]
      rw [hx']
      exact Subgroup.mem_map_of_mem π ha
  have hcomm_l : ⁅Xl, Xl⁆ ⊔ Ol = ⊤ := by
    refine (hmap_top_iff ⁅Xl, Xl⁆).mp ?_
    rw [Subgroup.map_commutator, hmapX, hperf_quot]
  have hcomm_G : ⁅X, X⁆ ⊔ CFSG.Open.pCoreOf 2 L = L := by
    calc ⁅X, X⁆ ⊔ CFSG.Open.pCoreOf 2 L
        = (⁅Xl, Xl⁆).map L.subtype ⊔ Ol.map L.subtype := by
          rw [Subgroup.map_commutator, hXl_map, hOl_map]
      _ = (⁅Xl, Xl⁆ ⊔ Ol).map L.subtype := by rw [Subgroup.map_sup]
      _ = (⊤ : Subgroup ↥L).map L.subtype := by rw [hcomm_l]
      _ = L := by rw [Subgroup.map_top, Subgroup.range_subtype]
  rcases lt_or_eq_of_le (Subgroup.commutator_le_self X) with hlt | heq
  · exact absurd hcomm_G (hmin ⁅X, X⁆ hlt)
  · exact heq

theorem map_pCore_eq_inf {G : Type} [Group G]
    (L X : Subgroup G) (hsup : X ⊔ CFSG.Open.pCoreOf 2 L = L) :
    (CFSG.pCore 2 ↥X).map X.subtype = X ⊓ CFSG.Open.pCoreOf 2 L := by
  classical
  have hXL : X ≤ L := by
    rw [← hsup]
    exact le_sup_left
  have hquot_bot : CFSG.pCore 2 (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) = ⊥ := by
    let π : ↥L →* CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L :=
      QuotientGroup.mk' (CFSG.pCore 2 ↥L)
    have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
    have hker : IsPGroup 2 π.ker := by
      rw [QuotientGroup.ker_mk']
      exact CFSG.pCore_isPGroup (p := 2) (G := ↥L)
    have hmap := CFSG.map_pCore_eq_of_surjective_of_isPGroup_ker (p := 2) π hπ hker
    rw [← hmap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  let f : ↥X →* CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hXL)
  have hf : Function.Surjective f := by
    simpa [f] using surjective_inclusion_comp_pCore_mk L X hXL hsup
  have hker : f.ker = (X ⊓ CFSG.Open.pCoreOf 2 L).subgroupOf X := by
    simpa [f] using ker_inclusion_comp_pCore_mk L X hXL
  have hker_le : f.ker ≤ (CFSG.Open.pCoreOf 2 L).subgroupOf X := by
    rw [hker]
    intro x hx
    exact hx.2
  have hker_p : IsPGroup 2 f.ker := by
    have hO_p : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype
    have hsub_p : IsPGroup 2 ((CFSG.Open.pCoreOf 2 L).subgroupOf X) := by
      change IsPGroup 2 ((CFSG.Open.pCoreOf 2 L).comap X.subtype)
      exact hO_p.comap_of_ker_isPGroup X.subtype
        (IsPGroup.ker_isPGroup_of_injective X.subtype_injective)
    exact hsub_p.to_le hker_le
  have hmapf := CFSG.map_pCore_eq_of_surjective_of_isPGroup_ker (p := 2) f hf hker_p
  rw [hquot_bot] at hmapf
  have hP : CFSG.pCore 2 ↥X ≤ f.ker :=
    (Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 ↥X) (f := f)).mp hmapf
  apply le_antisymm
  · calc (CFSG.pCore 2 ↥X).map X.subtype
        ≤ ((X ⊓ CFSG.Open.pCoreOf 2 L).subgroupOf X).map X.subtype :=
          Subgroup.map_mono (by rwa [hker] at hP)
      _ = X ⊓ CFSG.Open.pCoreOf 2 L := by
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
  · simpa [CFSG.Open.pCoreOf] using CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hXL

theorem nonempty_bar2_equiv_of_sup_pCore {G : Type} [Group G] [Finite G]
    (L X : Subgroup G) (hsup : X ⊔ CFSG.Open.pCoreOf 2 L = L) :
    Nonempty (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 X ≃*
      CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) := by
  classical
  have hXL : X ≤ L := by
    rw [← hsup]
    exact le_sup_left
  let f : ↥X →* CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hXL)
  have hf : Function.Surjective f := by
    simpa [f] using surjective_inclusion_comp_pCore_mk L X hXL hsup
  have hfk : f.ker = (X ⊓ CFSG.Open.pCoreOf 2 L).subgroupOf X := by
    simpa [f] using ker_inclusion_comp_pCore_mk L X hXL
  have hmap : (CFSG.pCore 2 ↥X).map X.subtype = X ⊓ CFSG.Open.pCoreOf 2 L :=
    map_pCore_eq_inf L X hsup
  have hker : f.ker = CFSG.pCore 2 ↥X := by
    rw [← Subgroup.map_subtype_inj (H := X), hfk, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr inf_le_left, hmap]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
