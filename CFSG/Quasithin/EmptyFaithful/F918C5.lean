module

import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Background.F918P5
public import CFSG.Quasithin.EmptyFaithful.S146B0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

section Bridge

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem pCore_le_ker_toAutI (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) :
    CFSG.pCore 2 ↥K ≤ (toAutI h I).ker := by
  have hF := factElem h hIU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  rw [MonoidHom.mem_ker, toAutI_eq_one_iff]
  apply h.actH_eq_one_of_mem_pCoreOf hIU
  have hx' : x ∈ CFSG.Open.pCore 2 ↥K := by
    assumption
  have hx1 : (x : G) ∈ pCoreOf 2 K := ⟨x, hx', rfl⟩
  exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp h.K_cComp) hx1

omit [Finite G] in
theorem coe_mem_pCoreOf_iff_mem_pCore (z : ↥K) : (z : G) ∈ pCoreOf 2 K ↔ z ∈ CFSG.pCore 2 ↥K :=
  CFSG.mem_openPCoreOf_iff z

theorem toAutI_ker_eq (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) (hne : autIH V₁ I H K ≠ ⊥) :
    (toAutI h I).ker = CFSG.pCore 2 ↥K := by
  have hF := factElem h hIU
  have hker := pCore_le_ker_toAutI h hIU
  refine le_antisymm ?_ hker
  intro x hx
  let f : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥(autIH V₁ I H K) := QuotientGroup.lift _ (toAutI h I) hker
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x', hx'⟩ := toAutI_surjective h I y
    exact ⟨QuotientGroup.mk x', hx'⟩
  have hinj : Function.Injective f := by
    have := hS
    apply injective_of_isSimpleGroup
    obtain ⟨y, hyS, hy1⟩ : ∃ y ∈ autIH V₁ I H K, y ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hne ((Subgroup.eq_bot_iff_forall _).mpr hcon)
    obtain ⟨s, hs⟩ := hsurj ⟨y, hyS⟩
    refine ⟨s, fun h1 => hy1 ?_⟩
    rw [h1] at hs
    exact congrArg Subtype.val hs.symm
  have h1 : f (QuotientGroup.mk x) = 1 := hx
  have h2 : (QuotientGroup.mk x : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := hinj (h1.trans (map_one f).symm)
  exact (QuotientGroup.eq_one_iff x).1 h2

theorem mem_pCoreOf_of_actH_eq_one_K (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) (hne : autIH V₁ I H K ≠ ⊥) {z : G} (hz : z ∈ K)
    (hzH : z ∈ H)
    (h1 : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨z, hzH⟩ = 1) :
    z ∈ pCoreOf 2 K := by
  have : (⟨z, hz⟩ : ↥K) ∈ (toAutI h I).ker := by
    rw [MonoidHom.mem_ker, toAutI_eq_one_iff]
    exact h1
  rw [toAutI_ker_eq h hIU hS hne] at this
  exact (coe_mem_pCoreOf_iff_mem_pCore (⟨z, hz⟩ : ↥K)).2 this

omit [Finite G] in
theorem actH_mem_normalizer_autIH (h : HypF918 T V L V₁ Vp H K) {s : G} (hsH : s ∈ H)
    (hsK : s ∈ Subgroup.normalizer (K : Set G)) :
    actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨s, hsH⟩ ∈
      Subgroup.normalizer ((autIH V₁ I H K : Subgroup _) : Set _) := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  set φ := actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hφ
  rw [Subgroup.mem_normalizer_iff]
  intro l
  rw [autIH_eq_map h hKH]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have hskK : s * (k : G) * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hsK _).mp hk'
    refine ⟨⟨s * (k : G) * s⁻¹, H.mul_mem (H.mul_mem hsH k.2) (H.inv_mem hsH)⟩,
      Subgroup.mem_subgroupOf.mpr hskK, ?_⟩
    show φ (⟨s, hsH⟩ * k * ⟨s, hsH⟩⁻¹) = _
    simp [map_mul, map_inv, hφ]
  · rintro ⟨k, hk, hkl⟩
    have hk' : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have hskK : s⁻¹ * (k : G) * s ∈ K := by
      apply (Subgroup.mem_normalizer_iff.mp hsK _).mpr
      simpa [mul_assoc] using hk'
    refine ⟨⟨s⁻¹ * (k : G) * s, H.mul_mem (H.mul_mem (H.inv_mem hsH) k.2) hsH⟩,
      Subgroup.mem_subgroupOf.mpr hskK, ?_⟩
    have e : φ ⟨s⁻¹ * (k : G) * s, H.mul_mem (H.mul_mem (H.inv_mem hsH) k.2) hsH⟩ =
        (φ ⟨s, hsH⟩)⁻¹ * φ k * φ ⟨s, hsH⟩ := by
      have : (⟨s⁻¹ * (k : G) * s, H.mul_mem (H.mul_mem (H.inv_mem hsH) k.2) hsH⟩ : ↥H) =
          ⟨s, hsH⟩⁻¹ * k * ⟨s, hsH⟩ := Subtype.ext (by simp)
      rw [this, map_mul, map_mul, map_inv]
    rw [e, hkl]
    group

omit [Finite G] in
theorem actH_mem_autIH_of_mem (h : HypF918 T V L V₁ Vp H K) {X : Subgroup G} (hXH : X ≤ H) {s : G}
    (hs : s ∈ X) :
    actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨s, hXH hs⟩ ∈ autIH V₁ I H X := by
  rw [autIH_eq_map h hXH]
  exact ⟨⟨s, hXH hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩

theorem actH_eq_one_of_mem_pCoreOf_K (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    {z : G} (hz : z ∈ pCoreOf 2 K) (hzH : z ∈ H) :
    actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨z, hzH⟩ = 1 := by
  have hF := factElem h hIU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact h.actH_eq_one_of_mem_pCoreOf hIU
    (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp h.K_cComp) hz)

theorem not_kbarInducesOuter_of_inner (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) (hne : autIH V₁ I H K ≠ ⊥) {s : G} (hsH : s ∈ H)
    (hsK : s ∈ Subgroup.normalizer (K : Set G))
    (hin : ∃ l₀ ∈ autIH V₁ I H K, ∀ x ∈ autIH V₁ I H K,
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨s, hsH⟩ * l₀⁻¹) * x =
        x * (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨s, hsH⟩ * l₀⁻¹)) :
    ¬ KbarInducesOuter K s := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  set φ := actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hφ
  obtain ⟨l₀, hl₀, hcomm⟩ := hin
  have hl₀' : l₀ ∈ (K.subgroupOf H).map φ := by
    rw [← autIH_eq_map h hKH]
    exact hl₀
  obtain ⟨k₀, hk₀, rfl⟩ := hl₀'
  have hk₀K : (k₀ : G) ∈ K := Subgroup.mem_subgroupOf.mp hk₀
  intro hout
  obtain ⟨x, hxK, hx⟩ := hout (k₀ : G) hk₀K
  apply hx
  have hsk : s * (k₀ : G)⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normalizer (K : Set G)).mul_mem hsK
      ((Subgroup.normalizer (K : Set G)).inv_mem (Subgroup.le_normalizer hk₀K))
  have hzK : ⁅s * (k₀ : G)⁻¹, x⁆ ∈ K := by
    have h1 : (s * (k₀ : G)⁻¹) * x * (s * (k₀ : G)⁻¹)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp hsk x).mp hxK
    rw [commutatorElement_def]
    exact K.mul_mem h1 (K.inv_mem hxK)
  have hzH : ⁅s * (k₀ : G)⁻¹, x⁆ ∈ H := hKH hzK
  refine mem_pCoreOf_of_actH_eq_one_K h hIU hS hne hzK hzH ?_
  rw [← hφ]
  have hxH : x ∈ H := hKH hxK
  have hxL : φ ⟨x, hxH⟩ ∈ autIH V₁ I H K := actH_mem_autIH_of_mem h hKH hxK
  have hc := hcomm _ hxL
  have e : (⟨⁅s * (k₀ : G)⁻¹, x⁆, hzH⟩ : ↥H) = ⁅(⟨s, hsH⟩ * k₀⁻¹ : ↥H), ⟨x, hxH⟩⁆ :=
    Subtype.ext (by simp [commutatorElement_def])
  rw [e, commutatorElement_def]
  simp only [map_mul, map_inv] at hc ⊢
  rw [hc]
  group

theorem not_kbarFusesThrees_of_class (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) (hne : autIH V₁ I H K ≠ ⊥) {s : G} (hsH : s ∈ H)
    (hsK : s ∈ Subgroup.normalizer (K : Set G))
    (hcls : ∀ x ∈ autIH V₁ I H K, x ^ 3 = 1 → ∃ l ∈ autIH V₁ I H K,
      l * x * l⁻¹ = actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨s, hsH⟩ * x *
        (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨s, hsH⟩)⁻¹) :
    ¬ KbarFusesThrees K s := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  set φ := actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hφ
  rintro ⟨x, hxK, hx3, -, hx⟩
  have hxH : x ∈ H := hKH hxK
  have hxL : φ ⟨x, hxH⟩ ∈ autIH V₁ I H K := actH_mem_autIH_of_mem h hKH hxK
  have hcube : (φ ⟨x, hxH⟩) ^ 3 = 1 := by
    have h3H : x ^ 3 ∈ H := H.pow_mem hxH 3
    have := actH_eq_one_of_mem_pCoreOf_K h hIU hx3 h3H
    have e : (⟨x ^ 3, h3H⟩ : ↥H) = ⟨x, hxH⟩ ^ 3 := Subtype.ext (by simp)
    rw [e, map_pow] at this
    exact this
  obtain ⟨l, hl, hle⟩ := hcls _ hxL hcube
  have hl' : l ∈ (K.subgroupOf H).map φ := by
    rw [← autIH_eq_map h hKH]
    exact hl
  obtain ⟨k₁, hk₁, rfl⟩ := hl'
  have hk₁K : (k₁ : G) ∈ K := Subgroup.mem_subgroupOf.mp hk₁
  apply hx (k₁ : G) hk₁K
  have hs1 : s * x * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hsK x).mp hxK
  have hk1 : (k₁ : G) * x * (k₁ : G)⁻¹ ∈ K := K.mul_mem (K.mul_mem hk₁K hxK) (K.inv_mem hk₁K)
  have hzK : ((k₁ : G) * x * (k₁ : G)⁻¹)⁻¹ * (s * x * s⁻¹) ∈ K := K.mul_mem (K.inv_mem hk1) hs1
  refine mem_pCoreOf_of_actH_eq_one_K h hIU hS hne hzK (hKH hzK) ?_
  rw [← hφ]
  have e : (⟨((k₁ : G) * x * (k₁ : G)⁻¹)⁻¹ * (s * x * s⁻¹), hKH hzK⟩ : ↥H) =
      (k₁ * ⟨x, hxH⟩ * k₁⁻¹)⁻¹ * (⟨s, hsH⟩ * ⟨x, hxH⟩ * ⟨s, hsH⟩⁻¹) := Subtype.ext (by simp)
  rw [e]
  simp only [map_mul, map_inv] at hle ⊢
  rw [hle]
  group

end Bridge

end CFSG.Quasithin
