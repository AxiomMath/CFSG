module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneAbar
import CFSG.GroupTheory.PGroup.LiftCoprimeQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
  (K6c LieFam811 IsLie811 IsSignedCoords IsSumZeroCoords)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Case811Sylow

variable {c : Ctx82E3 D}

lemma exists_conj_of_coords {V : Type*} [Group V] (h : Case811Sylow c)
    {c₀ : V →* c.Lbar} (a : V →* ↥c.L)
    (ha_range : a.range = h.A.subgroupOf c.L)
    (ha_apply : ∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v)
    (hXinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)).comp (h.A.subgroupOf c.L).subtype))
    (φ : V → V) {n : c.Lbar}
    (hn : n ∈ Subgroup.normalizer
      ((((h.A.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))) :
        Subgroup c.Lbar) : Set c.Lbar))
    (hform : ∀ v, n * c₀ v * n⁻¹ = c₀ (φ v)) :
    ∃ g : ↥c.L, (g : G) ∈ Subgroup.normalizer (h.A : Set G) ∧
      QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) g = n ∧
      ∀ v, (g : G) * ((a v : ↥c.L) : G) * (g : G)⁻¹ = ((a (φ v) : ↥c.L) : G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)
  obtain ⟨g, hgN, hgπ⟩ :=
    Ctx82E3.exists_mem_normalizer_of_mem_normalizer_lbar
      c (q := 3) (by norm_num) (h.A_le.trans h.P_le_L) (h.elemAbelian.isPGroup) hn
  have hgNX : g ∈ Subgroup.normalizer ((h.A.subgroupOf c.L) : Set ↥c.L) := by
    have hgSub : g ∈ (Subgroup.normalizer (h.A : Set G)).subgroupOf c.L :=
      Subgroup.mem_subgroupOf.mpr hgN
    rwa [Subgroup.subgroupOf_normalizer_eq (h.A_le.trans h.P_le_L)] at hgSub
  refine ⟨g, hgN, hgπ, ?_⟩
  intro v
  have havX : a v ∈ h.A.subgroupOf c.L := by
    have h : a v ∈ a.range := MonoidHom.mem_range.mpr ⟨v, rfl⟩
    rwa [ha_range] at h
  let x : ↥c.L := g * a v * g⁻¹
  have hxX : x ∈ h.A.subgroupOf c.L :=
    (Subgroup.mem_normalizer_iff.mp hgNX (a v)).mp havX
  have hφX : a (φ v) ∈ h.A.subgroupOf c.L := by
    have h : a (φ v) ∈ a.range := MonoidHom.mem_range.mpr ⟨φ v, rfl⟩
    rwa [ha_range] at h
  have himg : π x = π (a (φ v)) := by
    show π (g * a v * g⁻¹) = π (a (φ v))
    rw [map_mul, map_mul, map_inv, hgπ, ha_apply, hform, ha_apply]
  have hxeq : x = a (φ v) := by
    have hsub : (⟨x, hxX⟩ : h.A.subgroupOf c.L) =
        ⟨a (φ v), hφX⟩ := hXinj (by simpa [π] using himg)
    exact congrArg Subtype.val hsub
  have := congrArg (fun z : ↥c.L => (z : G)) hxeq
  simpa [x] using this

theorem mem_normalizer_of_coords (h : Case811Sylow c) {V : Type*} [Group V] {c₀ : V →* c.Lbar}
    (hc₀range : c₀.range = h.Abar) {n : c.Lbar} {φ : V → V}
    (hform : ∀ v, n * c₀ v * n⁻¹ = c₀ (φ v)) :
    n ∈ Subgroup.normalizer (h.Abar : Set c.Lbar) := by
  refine Subgroup.mem_normalizer_fintype ?_
  intro x hx
  rw [← hc₀range] at hx ⊢
  obtain ⟨v, rfl⟩ := hx
  exact ⟨φ v, (hform v).symm⟩

private lemma ofAdd_pow_three {n : ℕ} (v : Fin n → ZMod 3) :
    (Multiplicative.ofAdd v : Multiplicative (Fin n → ZMod 3)) ^ 3 = 1 := by
  rw [← ofAdd_nsmul]
  have hzero : (3 : ℕ) • v = 0 := by
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    have h3 : (↑(3 : ℕ) : ZMod 3) = 0 := by rfl
    rw [h3, zero_mul]
  rw [hzero, ofAdd_zero]

theorem exists_coords_lift (h : Case811Sylow c) {V : Type*}
    [Group V] {c₀ : V →* c.Lbar} (hrange : c₀.range = h.Abar) :
    ∃ a : V →* ↥c.L,
      a.range = h.A.subgroupOf c.L ∧
      (∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v) ∧
      Function.Injective ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)).comp
        (h.A.subgroupOf c.L).subtype) ∧
      (∀ v, (a v : G) ∈ h.A) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  have hN3 : ¬ 3 ∣ Nat.card N :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) Nat.prime_three (by norm_num)
  have hX3 : IsPGroup 3 (h.A.subgroupOf c.L) := h.elemAbelian.isPGroup.comap_subtype (K := c.L)
  have hXinj : Function.Injective (π.comp (h.A.subgroupOf c.L).subtype) :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 3) (N := N)
      (Q := h.A.subgroupOf c.L) hN3 hX3
  obtain ⟨a, ha_range, ha_apply⟩ :=
    CFSG.GroupTheory.exists_lift_of_isPGroup_of_not_dvd_card (N := N) hN3 hX3
      (X := h.A.subgroupOf c.L) (Xbar := h.Abar) rfl c₀ hrange
  have ha_memX : ∀ v, a v ∈ h.A.subgroupOf c.L := by
    intro v
    have hv : a v ∈ a.range := MonoidHom.mem_range.mpr ⟨v, rfl⟩
    rwa [ha_range] at hv
  have ha_memA : ∀ v, (a v : G) ∈ h.A := by
    intro v
    have hmem : (a v : G) ∈ (h.A.subgroupOf c.L).map c.L.subtype :=
      Subgroup.mem_map_of_mem c.L.subtype (ha_memX v)
    rwa [Subgroup.map_subgroupOf_eq_of_le (h.A_le.trans h.P_le_L)] at hmem
  exact ⟨a, ha_range, ha_apply, hXinj, ha_memA⟩

theorem signed_coords_setup (h : Case811Sylow c) (hK6c : K6c)
    {fam : LieFam811} {r f : ℕ} (hlie : IsLie811 c.Lbar fam r f) (hfam : fam ≠ .l4) :
    ∃ (c₀ : Multiplicative (Fin 3 → ZMod 3) →* c.Lbar)
      (a : Multiplicative (Fin 3 → ZMod 3) →* ↥c.L),
      IsSignedCoords h.Abar c₀ ∧
      a.range = h.A.subgroupOf c.L ∧
      (∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v) ∧
      Function.Injective ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)).comp
        (h.A.subgroupOf c.L).subtype) ∧
      Function.Injective a ∧
      (∀ v, (a v : G) ∈ h.A) ∧
      (∀ v : Fin 3 → ZMod 3, v ≠ 0 →
        orderOf ((a (Multiplicative.ofAdd v) : ↥c.L) : G) = 3) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨c₀, hc₀⟩ := (hK6c c.Lbar fam r f hlie h.Abar h.isElemAbelian_Abar h.card_Abar).2 hfam
  obtain ⟨a, ha_range, ha_apply, hXinj, ha_memA⟩ := exists_coords_lift h hc₀.2.1
  have ha_inj : Function.Injective a := by
    intro u v huv
    apply hc₀.1
    have h : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a u) =
        QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) := congrArg _ huv
    rwa [ha_apply u, ha_apply v] at h
  have ha_order : ∀ v : Fin 3 → ZMod 3, v ≠ 0 →
      orderOf ((a (Multiplicative.ofAdd v) : ↥c.L) : G) = 3 := by
    intro v hv
    have hvne : (Multiplicative.ofAdd v : Multiplicative (Fin 3 → ZMod 3)) ≠ 1 := by
      intro hone
      exact hv (ofAdd_eq_one.mp hone)
    rw [Subgroup.orderOf_coe, orderOf_injective a ha_inj, orderOf_eq_prime (ofAdd_pow_three v) hvne]
  exact ⟨c₀, a, hc₀, ha_range, ha_apply, hXinj, ha_inj, ha_memA, ha_order⟩

theorem sumZero_coords_setup (h : Case811Sylow c) (hK6c : K6c)
    {fam : LieFam811} {r f : ℕ} (hlie : IsLie811 c.Lbar fam r f) (hfam : fam = .l4) :
    ∃ (c₀ : Multiplicative (Fin 4 → ZMod 3) →* c.Lbar)
      (a : Multiplicative (Fin 4 → ZMod 3) →* ↥c.L),
      IsSumZeroCoords h.Abar c₀ ∧
      a.range = h.A.subgroupOf c.L ∧
      (∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v) ∧
      Function.Injective ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)).comp
        (h.A.subgroupOf c.L).subtype) ∧
      (∀ v, a v = 1 ↔ c₀ v = 1) ∧
      (∀ v, (a v : G) ∈ h.A) ∧
      (∀ v : Fin 4 → ZMod 3, (¬ ∃ d : ZMod 3, v = fun _ => d) →
        orderOf ((a (Multiplicative.ofAdd v) : ↥c.L) : G) = 3) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨c₀, hc₀⟩ := (hK6c c.Lbar fam r f hlie h.Abar h.isElemAbelian_Abar h.card_Abar).1 hfam
  obtain ⟨a, ha_range, ha_apply, hXinj, ha_memA⟩ := exists_coords_lift h hc₀.1
  have ha_memX : ∀ v, a v ∈ h.A.subgroupOf c.L := by
    intro v
    have hv : a v ∈ a.range := MonoidHom.mem_range.mpr ⟨v, rfl⟩
    rwa [ha_range] at hv
  have ha_eq_one_iff : ∀ v, a v = 1 ↔ c₀ v = 1 := by
    intro v
    constructor
    · intro hv
      rw [← ha_apply v, hv, map_one]
    · intro hv
      have h : (⟨a v, ha_memX v⟩ : h.A.subgroupOf c.L) =
          ⟨1, (h.A.subgroupOf c.L).one_mem⟩ := hXinj (by
        show QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) =
          QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (1 : ↥c.L)
        rw [ha_apply v, hv, map_one])
      exact congrArg Subtype.val h
  have ha_order : ∀ v : Fin 4 → ZMod 3, (¬ ∃ d : ZMod 3, v = fun _ => d) →
      orderOf ((a (Multiplicative.ofAdd v) : ↥c.L) : G) = 3 := by
    intro v hv
    have hvne : (Multiplicative.ofAdd v : Multiplicative (Fin 4 → ZMod 3)) ≠ 1 := by
      intro hone
      apply hv
      have h1 : c₀ (Multiplicative.ofAdd v) = 1 := by
        rw [← ha_apply (Multiplicative.ofAdd v), hone]
        simp
      exact (hc₀.2.1 (Multiplicative.ofAdd v)).mp h1
    refine orderOf_eq_prime ?_ ?_
    · have h : ((a (Multiplicative.ofAdd v) : ↥c.L) : G) ^ 3 =
          ((a ((Multiplicative.ofAdd v) ^ 3) : ↥c.L) : G) := by
        rw [map_pow]
        rfl
      rw [h, ofAdd_pow_three v, map_one]
      rfl
    · intro h1
      exact hv ((hc₀.2.1 (Multiplicative.ofAdd v)).mp
        ((ha_eq_one_iff (Multiplicative.ofAdd v)).mp (Subtype.ext h1)))
  exact ⟨c₀, a, hc₀, ha_range, ha_apply, hXinj, ha_eq_one_iff, ha_memA, ha_order⟩

end Case811Sylow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
