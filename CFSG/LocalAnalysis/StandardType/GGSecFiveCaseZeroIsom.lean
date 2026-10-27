module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroCoordDefs
public import CFSG.LocalAnalysis.StandardType.GGDepARefl

public section

namespace CFSG.StandardType

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {m : ℕ}

private noncomputable def czFormDual (φ : Fin m → Module.Dual (ZMod p) V) (x : V) :
    Module.Dual (ZMod p) V where
  toFun := fun v => ggCZForm φ v x
  map_add' := by
    intro v w
    exact ggCZForm_add_left v w x
  map_smul' := by
    intro c v
    exact ggCZForm_smul_left c v x

private theorem czFormDual_apply {φ : Fin m → Module.Dual (ZMod p) V} (x v : V) :
    czFormDual φ x v = ggCZForm φ v x := rfl

private theorem cz_form_e_e {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (i j : Fin m) :
    ggCZForm φ (e i) (e j) = if i = j then 1 else 0 := by
  rw [ggCZForm_apply_e hd (e i) j, hd j i]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

private def czIsRoot (e : Fin m → V) (_φ : Fin m → Module.Dual (ZMod p) V) (x : V) : Prop :=
  ∃ i j : Fin m, i ≠ j ∧ ∃ ε : ZMod p, (ε = 1 ∨ ε = -1) ∧ x = e i - ε • e j

private theorem cz_root_ne_zero {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {x : V} (hx : czIsRoot e φ x) : x ≠ 0 := by
  obtain ⟨i, j, hij, ε, hε, rfl⟩ := hx
  intro h
  have h1 : φ i (e i - ε • e j) = 1 := by
    rw [map_sub, LinearMap.map_smul, hd i i, hd i j, if_pos rfl, if_neg hij,
      smul_zero, sub_zero]
  rw [h, map_zero] at h1
  exact one_ne_zero h1.symm

private theorem cz_form_apply_root {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (v : V) {i j : Fin m} {ε : ZMod p} :
    ggCZForm φ v (e i - ε • e j) = φ i v - ε * φ j v := by
  rw [ggCZForm_sub_right, ggCZForm_smul_right, ggCZForm_apply_e hd v i, ggCZForm_apply_e hd v j]

private theorem cz_form_root_self {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {i j : Fin m} (hij : i ≠ j) {ε : ZMod p}
    (hε : ε = 1 ∨ ε = -1) :
    ggCZForm φ (e i - ε • e j) (e i - ε • e j) = 2 := by
  have hi : φ i (e i - ε • e j) = 1 := by
    rw [map_sub, LinearMap.map_smul, hd i i, hd i j, if_pos rfl, if_neg hij,
      smul_zero, sub_zero]
  have hj : φ j (e i - ε • e j) = -ε := by
    rw [map_sub, LinearMap.map_smul, hd j i, hd j j, if_neg (Ne.symm hij), if_pos rfl,
      smul_eq_mul, mul_one, zero_sub]
  rw [cz_form_apply_root hd _, hi, hj]
  have hε2 : ε * ε = 1 := by
    rcases hε with h | h
    · rw [h, one_mul]
    · rw [h, neg_mul_neg, one_mul]
  calc (1 : ZMod p) - ε * (-ε) = 1 + ε * ε := by
        rw [mul_neg, sub_neg_eq_add]
    _ = 1 + 1 := by rw [hε2]
    _ = 2 := by rw [one_add_one_eq_two]

private theorem cz_neg_one_ne_zero : (-1 : ZMod p) ≠ 0 := by
  intro h
  have h1 : (1 : ZMod p) = 0 := neg_eq_zero.mp h
  rw [ZMod.one_eq_zero_iff] at h1
  exact (Fact.out : p.Prime).ne_one h1

private theorem cz_neg_two_ne_zero (hp2 : p ≠ 2) : (-2 : ZMod p) ≠ 0 := by
  intro h
  exact zmod_two_ne_zero hp2 (neg_eq_zero.mp h)

private theorem cz_form_root_self' {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {x : V} (hx : czIsRoot e φ x) : ggCZForm φ x x = 2 := by
  obtain ⟨i, j, hij, ε, hε, rfl⟩ := hx
  exact cz_form_root_self hd hij hε

private theorem cz_form_two_roots {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (A B C D : ZMod p) (i j k l : Fin m) :
    ggCZForm φ (A • e i - B • e j) (C • e k - D • e l) =
      A * C * (if i = k then 1 else 0) - A * D * (if i = l then 1 else 0) -
      B * C * (if j = k then 1 else 0) + B * D * (if j = l then 1 else 0) := by
  simp only [ggCZForm_sub_left, ggCZForm_sub_right, ggCZForm_smul_left,
    ggCZForm_smul_right, cz_form_e_e hd]
  ring

private theorem cz_form_root_diff {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {i j : Fin m} {ε : ZMod p} (k l : Fin m) :
    ggCZForm φ (e i - ε • e j) (e k - e l) =
      (if i = k then 1 else 0) - (if i = l then 1 else 0) -
        ε * (if j = k then 1 else 0) + ε * (if j = l then 1 else 0) := by
  have h := cz_form_two_roots hd (1 : ZMod p) ε 1 1 i j k l
  simpa using h

private theorem cz_form_diff_diff {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (i j k l : Fin m) :
    ggCZForm φ (e i - e j) (e k - e l) =
      (if i = k then 1 else 0) - (if i = l then 1 else 0) -
        (if j = k then 1 else 0) + (if j = l then 1 else 0) := by
  have h := cz_form_root_diff (hd := hd) (i := i) (j := j) (ε := 1) k l
  simpa using h

private noncomputable def czProj (e : Fin m → V)
    (φ : Fin m → Module.Dual (ZMod p) V) : V →ₗ[ZMod p] V where
  toFun := fun v => ∑ k, φ k v • e k
  map_add' := by
    intro x y
    simp only [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp only [LinearMap.map_smul, smul_eq_mul, RingHom.id_apply, mul_smul,
      Finset.smul_sum]

private theorem czProj_apply {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V} (v : V) :
    czProj e φ v = ∑ k, φ k v • e k := rfl

private theorem czProj_e {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (i : Fin m) : czProj e φ (e i) = e i := by
  rw [czProj_apply]
  rw [Finset.sum_eq_single i]
  · rw [hd i i, if_pos rfl, one_smul]
  · intro b _ hb
    rw [hd b i, if_neg hb, zero_smul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private theorem czProj_φ {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (k : Fin m) (v : V) : φ k (czProj e φ v) = φ k v := by
  have hd' : ∀ i, φ k (e i) = if k = i then 1 else 0 := hd k
  rw [czProj_apply, map_sum]
  simp only [LinearMap.map_smul, smul_eq_mul, hd', mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

private noncomputable def czCoord (e : Fin m → V)
    (φ : Fin m → Module.Dual (ZMod p) V) : Submodule (ZMod p) V :=
  LinearMap.ker (czProj e φ - LinearMap.id)

private theorem czCoord_mem_iff {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (u : V) : u ∈ czCoord e φ ↔ czProj e φ u = u := by
  rw [czCoord, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

private theorem czCoord_e {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (i : Fin m) : e i ∈ czCoord e φ := by
  rw [czCoord_mem_iff, czProj_e hd i]

private theorem czCoord_root {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {x : V} (hx : czIsRoot e φ x) : x ∈ czCoord e φ := by
  obtain ⟨i, j, hij, ε, hε, rfl⟩ := hx
  have hi : e i ∈ czCoord e φ := czCoord_e hd i
  have hj : e j ∈ czCoord e φ := czCoord_e hd j
  exact (czCoord e φ).sub_mem hi ((czCoord e φ).smul_mem ε hj)

private def czSpan (e : Fin m → V) (_φ : Fin m → Module.Dual (ZMod p) V) :
    Submodule (ZMod p) V :=
  Submodule.span (ZMod p) (Set.range e)

private theorem czProj_mem_span {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (v : V) : czProj e φ v ∈ czSpan e φ := by
  rw [czProj_apply]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

private theorem cz_exists_pair (hm : 2 ≤ m) : ∃ a b : Fin m, a ≠ b := by
  have hne : Nonempty (Fin m) := Fintype.card_pos_iff.mp (by
    rw [Fintype.card_fin]
    omega)
  let a : Fin m := Classical.choice hne
  have h1 : 1 < Fintype.card (Fin m) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card h1 a
  exact ⟨b, a, hb⟩

private theorem cz_exists_ne (hm : 2 ≤ m) (k : Fin m) : ∃ l : Fin m, l ≠ k := by
  have h1 : 1 < Fintype.card (Fin m) := by
    rw [Fintype.card_fin]
    omega
  exact Fintype.exists_ne_of_one_lt_card h1 k

private theorem cz_exists_third (hm : 3 ≤ m) {i j : Fin m} (hij : i ≠ j) :
    ∃ s : Fin m, s ≠ i ∧ s ≠ j := by
  have hmem : j ∈ ((Finset.univ : Finset (Fin m)).erase i) := by
    rw [Finset.mem_erase]
    exact ⟨hij.symm, Finset.mem_univ j⟩
  have hpos : 0 < (((Finset.univ : Finset (Fin m)).erase i).erase j).card := by
    rw [Finset.card_erase_of_mem hmem,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
  exact ⟨s, Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hs),
    Finset.ne_of_mem_erase hs⟩

private theorem cz_exists_two_ne (hm : 3 ≤ m) (i : Fin m) :
    ∃ j k : Fin m, j ≠ i ∧ k ≠ i ∧ j ≠ k := by
  have hcard : ((Finset.univ : Finset (Fin m)).erase i).card = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
  obtain ⟨j, hj⟩ :=
    Finset.card_pos.mp (by omega : 0 < ((Finset.univ : Finset (Fin m)).erase i).card)
  have hpos : 0 < (((Finset.univ : Finset (Fin m)).erase i).erase j).card := by
    rw [Finset.card_erase_of_mem hj]
    omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  exact ⟨j, k, Finset.ne_of_mem_erase hj,
    Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk),
    (Finset.ne_of_mem_erase hk).symm⟩

private theorem cz_refl_mem {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {x : V} (hx : czIsRoot e φ x) :
    ∃ r : V ≃ₗ[ZMod p] V, r ∈ ggCZRD e φ ∧
      ∀ v, r v = v - ggCZForm φ v x • x := by
  obtain ⟨i, j, hij, ε, hε, rfl⟩ := hx
  have hfx : czFormDual φ (e i - ε • e j) (e i - ε • e j) = 2 := by
    rw [czFormDual_apply]
    exact cz_form_root_self hd hij hε
  refine ⟨Module.reflection hfx, ?_, ?_⟩
  · refine ⟨i, j, hij, ε, hε, fun v => ?_⟩
    rw [Module.reflection_apply, czFormDual_apply, cz_form_apply_root hd v]
  · intro v
    rw [Module.reflection_apply, czFormDual_apply]

private theorem cz_mem_data {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {r : V ≃ₗ[ZMod p] V} (hr : r ∈ ggCZRD e φ) :
    ∃ x : V, czIsRoot e φ x ∧ IsLinRefl r ∧
      ∀ v, r v = v - ggCZForm φ v x • x := by
  obtain ⟨i, j, hij, ε, hε, hr'⟩ := hr
  refine ⟨e i - ε • e j, ⟨i, j, hij, ε, hε, rfl⟩, ?_, ?_⟩
  · refine ⟨e i - ε • e j, czFormDual φ (e i - ε • e j), ?_, fun v => ?_⟩
    · rw [czFormDual_apply]
      exact cz_form_root_self hd hij hε
    · rw [hr' v, czFormDual_apply, cz_form_apply_root hd v]
  · intro v
    rw [hr' v, cz_form_apply_root hd v]

private noncomputable def czLambda (φ : Fin m → Module.Dual (ZMod p) V)
    (t : V ≃ₗ[ZMod p] V) (x : V) : ZMod p :=
  ggCZForm φ (t x) (t x) / 2

private theorem cz_image_root_data {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (hp2 : p ≠ 2) {t : V ≃ₗ[ZMod p] V}
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ) {α : V} (hα : czIsRoot e φ α) :
    ∃ (β : V) (c : ZMod p), czIsRoot e φ β ∧ c ≠ 0 ∧ t α = c • β ∧
      ∀ w, ggCZForm φ (t w) β = c * ggCZForm φ w α := by
  obtain ⟨r, hrmem, hrform⟩ := cz_refl_mem hd hα
  have hα0 : α ≠ 0 := cz_root_ne_zero hd hα
  have hconj : (t * r * t⁻¹) ∈ ggCZRD e φ := hN r hrmem
  obtain ⟨β, hβroot, hr'refl, hr'form⟩ := cz_mem_data hd hconj
  have hβ0 : β ≠ 0 := cz_root_ne_zero hd hβroot
  have hrα : r α = -α := by
    rw [hrform, cz_form_root_self' hd hα, two_smul]
    abel
  have hanti : (t * r * t⁻¹) (t α) = -(t α) := by
    have h1 : (t * r * t⁻¹) (t α) = t (r α) := by
      change t (r (t.symm (t α))) = t (r α)
      rw [LinearEquiv.symm_apply_apply]
    rw [h1, hrα, map_neg]
  have hβanti : (t * r * t⁻¹) β = -β := by
    rw [hr'form, cz_form_root_self' hd hβroot, two_smul]
    abel
  have htα0 : t α ≠ 0 := by
    intro h
    exact hα0 (t.injective (by rw [h, map_zero]))
  obtain ⟨d, hd'⟩ := hr'refl.anti_eq_smul hp2 htα0 hanti hβanti
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, zero_smul] at hd'
    exact hβ0 hd'
  let c : ZMod p := d⁻¹
  have hc0 : c ≠ 0 := inv_ne_zero hd0
  have hc : t α = c • β := by
    rw [show β = d • t α from hd']
    change t α = d⁻¹ • (d • t α)
    rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
  refine ⟨β, c, hβroot, hc0, hc, ?_⟩
  intro w
  have hL : (t * r * t⁻¹) (t w) = t w - ggCZForm φ (t w) β • β := hr'form (t w)
  have hR : t (r w) = t w - (ggCZForm φ w α * c) • β := by
    rw [hrform w, map_sub, LinearEquiv.map_smul, hc, smul_smul]
  have h1 : (t * r * t⁻¹) (t w) = t (r w) := by
    change t (r (t.symm (t w))) = t (r w)
    rw [LinearEquiv.symm_apply_apply]
  rw [hL, hR] at h1
  have h2 : ggCZForm φ (t w) β • β = (ggCZForm φ w α * c) • β :=
    sub_right_inj.mp h1
  have h3 : ggCZForm φ (t w) β = ggCZForm φ w α * c :=
    (smul_left_inj hβ0).mp h2
  rw [h3, mul_comm]

private theorem cz_image_root {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (hp2 : p ≠ 2) {t : V ≃ₗ[ZMod p] V}
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ) {α : V} (hα : czIsRoot e φ α) :
    ∃ β : V, czIsRoot e φ β ∧ ∃ c : ZMod p, c ≠ 0 ∧ t α = c • β := by
  obtain ⟨β, c, hβroot, hc0, hc, _⟩ := cz_image_root_data hd hp2 hN hα
  exact ⟨β, hβroot, c, hc0, hc⟩

private theorem czCoord_image_root {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (hp2 : p ≠ 2) {t : V ≃ₗ[ZMod p] V}
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ) {α : V} (hα : czIsRoot e φ α) :
    t α ∈ czCoord e φ := by
  obtain ⟨β, hβroot, c, hc0, hc⟩ := cz_image_root hd hp2 hN hα
  rw [hc]
  exact (czCoord e φ).smul_mem c (czCoord_root hd hβroot)

private theorem cz_form_t_image {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (hp2 : p ≠ 2) {t : V ≃ₗ[ZMod p] V}
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ) {α : V} (hα : czIsRoot e φ α)
    (w : V) : ggCZForm φ (t w) (t α) = czLambda φ t α * ggCZForm φ w α := by
  obtain ⟨β, c, hβroot, hc0, hc, hbw⟩ := cz_image_root_data hd hp2 hN hα
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hpow : czLambda φ t α = c * c := by
    rw [czLambda, hc, ggCZForm_smul_left, ggCZForm_smul_right,
      cz_form_root_self' hd hβroot]
    rw [show c * (c * 2) = c * c * 2 by ring]
    exact mul_div_cancel_right₀ (c * c) h2
  calc ggCZForm φ (t w) (t α) = ggCZForm φ (t w) (c • β) := by rw [hc]
    _ = c * ggCZForm φ (t w) β := ggCZForm_smul_right c (t w) β
    _ = c * (c * ggCZForm φ w α) := by rw [hbw w]
    _ = c * c * ggCZForm φ w α := by ring
    _ = czLambda φ t α * ggCZForm φ w α := by rw [hpow]

private theorem cz_lambda_eq_of_ne {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (hp2 : p ≠ 2) {t : V ≃ₗ[ZMod p] V}
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ) {α γ : V}
    (hα : czIsRoot e φ α) (hγ : czIsRoot e φ γ) (h : ggCZForm φ α γ ≠ 0) :
    czLambda φ t α = czLambda φ t γ := by
  have h1 := cz_form_t_image hd hp2 hN hα γ
  have h2 := cz_form_t_image hd hp2 hN hγ α
  have hsym : ggCZForm φ (t γ) (t α) = ggCZForm φ (t α) (t γ) :=
    ggCZForm_comm (t γ) (t α)
  rw [h1, h2, ggCZForm_comm γ α] at hsym
  have hzero : (czLambda φ t α - czLambda φ t γ) * ggCZForm φ α γ = 0 := by
    rw [sub_mul, hsym, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right h)

private theorem cz_lambda_same_first {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (hp2 : p ≠ 2) (hm : 3 ≤ m) {t : V ≃ₗ[ZMod p] V}
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ)
    {i j : Fin m} (hij : i ≠ j) {ε : ZMod p} (hε : ε = 1 ∨ ε = -1) :
    czLambda φ t (e i - ε • e j) = czLambda φ t (e i - e j) := by
  rcases hε with hε | hε
  · rw [hε, one_smul]
  · rw [hε]
    obtain ⟨s, hsi, hsj⟩ := cz_exists_third hm hij
    have hroot1 : czIsRoot e φ (e i - (-1 : ZMod p) • e j) :=
      ⟨i, j, hij, -1, Or.inr rfl, rfl⟩
    have hroot2 : czIsRoot e φ (e i - e s) :=
      ⟨i, s, hsi.symm, 1, Or.inl rfl, by simp⟩
    have hroot3 : czIsRoot e φ (e i - e j) :=
      ⟨i, j, hij, 1, Or.inl rfl, by simp⟩
    have h1 : czLambda φ t (e i - (-1 : ZMod p) • e j) =
        czLambda φ t (e i - e s) := by
      apply cz_lambda_eq_of_ne hd hp2 hN hroot1 hroot2
      have hB : ggCZForm φ (e i - (-1 : ZMod p) • e j) (e i - e s) = 1 := by
        rw [cz_form_root_diff hd]
        simp [Ne.symm hsi, Ne.symm hsj, Ne.symm hij]
      rw [hB]
      exact one_ne_zero
    have h2 : czLambda φ t (e i - e j) = czLambda φ t (e i - e s) := by
      apply cz_lambda_eq_of_ne hd hp2 hN hroot3 hroot2
      have hB : ggCZForm φ (e i - e j) (e i - e s) = 1 := by
        rw [cz_form_diff_diff hd]
        simp [Ne.symm hsi, Ne.symm hsj, Ne.symm hij]
      rw [hB]
      exact one_ne_zero
    rw [h1, h2]

private theorem cz_lambda_diff_eq {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (hp2 : p ≠ 2) {t : V ≃ₗ[ZMod p] V}
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ) {i j k l : Fin m}
    (hij : i ≠ j) (hkl : k ≠ l) :
    czLambda φ t (e i - e j) = czLambda φ t (e k - e l) := by
  have hroot1 : czIsRoot e φ (e i - e j) := ⟨i, j, hij, 1, Or.inl rfl, by simp⟩
  have hroot2 : czIsRoot e φ (e k - e l) := ⟨k, l, hkl, 1, Or.inl rfl, by simp⟩
  by_cases hik : i = k
  · subst hik
    by_cases hjl : j = l
    · subst hjl
      rfl
    · apply cz_lambda_eq_of_ne hd hp2 hN hroot1 hroot2
      have hB : ggCZForm φ (e i - e j) (e i - e l) = 1 := by
        rw [cz_form_diff_diff hd]
        simp [hkl, Ne.symm hij, hjl]
      rw [hB]
      exact one_ne_zero
  · by_cases hil : i = l
    · subst hil
      by_cases hjk : j = k
      · subst hjk
        apply cz_lambda_eq_of_ne hd hp2 hN hroot1 hroot2
        have hB : ggCZForm φ (e i - e j) (e j - e i) = -2 := by
          rw [cz_form_diff_diff hd]
          simp [hij, Ne.symm hij]
          ring_nf
        rw [hB]
        exact cz_neg_two_ne_zero hp2
      · apply cz_lambda_eq_of_ne hd hp2 hN hroot1 hroot2
        have hB : ggCZForm φ (e i - e j) (e k - e i) = -1 := by
          rw [cz_form_diff_diff hd]
          simp [Ne.symm hij, hik, hjk]
        rw [hB]
        exact cz_neg_one_ne_zero
    · by_cases hjk : j = k
      · subst hjk
        apply cz_lambda_eq_of_ne hd hp2 hN hroot1 hroot2
        have hB : ggCZForm φ (e i - e j) (e j - e l) = -1 := by
          rw [cz_form_diff_diff hd]
          simp [hij, hil, hkl]
        rw [hB]
        exact cz_neg_one_ne_zero
      · by_cases hjl : j = l
        · subst hjl
          apply cz_lambda_eq_of_ne hd hp2 hN hroot1 hroot2
          have hB : ggCZForm φ (e i - e j) (e k - e j) = 1 := by
            rw [cz_form_diff_diff hd]
            simp [hik, hil, hjk]
          rw [hB]
          exact one_ne_zero
        · have hrootm : czIsRoot e φ (e i - e k) :=
            ⟨i, k, hik, 1, Or.inl rfl, by simp⟩
          have hB1 : ggCZForm φ (e i - e j) (e i - e k) = 1 := by
            rw [cz_form_diff_diff hd]
            simp [Ne.symm hij, hik, hjk]
          have hB2 : ggCZForm φ (e k - e l) (e i - e k) = -1 := by
            rw [cz_form_diff_diff hd]
            simp [Ne.symm hik, Ne.symm hil, Ne.symm hkl]
          rw [cz_lambda_eq_of_ne hd hp2 hN hroot1 hrootm (by rw [hB1]; exact one_ne_zero),
            cz_lambda_eq_of_ne hd hp2 hN hroot2 hrootm (by rw [hB2]; exact cz_neg_one_ne_zero)]

private theorem cz_lambda_eq {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (hp2 : p ≠ 2) (hm : 3 ≤ m) {t : V ≃ₗ[ZMod p] V}
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ)
    {α γ : V} (hα : czIsRoot e φ α) (hγ : czIsRoot e φ γ) :
    czLambda φ t α = czLambda φ t γ := by
  obtain ⟨i, j, hij, ε, hε, rfl⟩ := hα
  obtain ⟨k, l, hkl, δ, hδ, rfl⟩ := hγ
  rw [cz_lambda_same_first hd hp2 hm hN hij hε,
    cz_lambda_same_first hd hp2 hm hN hkl hδ]
  exact cz_lambda_diff_eq hd hp2 hN hij hkl

private theorem cz_lambda_eq_ref {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (hp2 : p ≠ 2) (hm : 3 ≤ m) {t : V ≃ₗ[ZMod p] V}
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ)
    {a b : Fin m} (hab : a ≠ b) {α : V} (hα : czIsRoot e φ α) :
    czLambda φ t α = czLambda φ t (e a - e b) :=
  cz_lambda_eq hd hp2 hm hN hα ⟨a, b, hab, 1, Or.inl rfl, by simp⟩

private def czRel (φ : Fin m → Module.Dual (ZMod p) V) (t : V ≃ₗ[ZMod p] V)
    (lam : ZMod p) (v : V) : Submodule (ZMod p) V where
  carrier := {u | ggCZForm φ (t v) (t u) = lam * ggCZForm φ v u}
  zero_mem' := by simp [ggCZForm]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, ggCZForm_add_right, ha, hb, ggCZForm_add_right, mul_add]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_smul, ggCZForm_smul_right, ha, ggCZForm_smul_right]
    ring

private theorem cz_form_t_span {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (hp2 : p ≠ 2) (hm : 3 ≤ m) {t : V ≃ₗ[ZMod p] V}
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ)
    {a b : Fin m} (hab : a ≠ b) {v u : V} (hu : u ∈ czSpan e φ) :
    ggCZForm φ (t v) (t u) = czLambda φ t (e a - e b) * ggCZForm φ v u := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hmem : ∀ k : Fin m, e k ∈ czRel φ t (czLambda φ t (e a - e b)) v := by
    intro k
    obtain ⟨l, hl⟩ := cz_exists_ne (by omega : 2 ≤ m) k
    have hroot1 : czIsRoot e φ (e k - e l) :=
      ⟨k, l, hl.symm, 1, Or.inl rfl, by simp⟩
    have hroot2 : czIsRoot e φ (e k + e l) := by
      refine ⟨k, l, hl.symm, -1, Or.inr rfl, ?_⟩
      rw [neg_smul, one_smul, sub_neg_eq_add]
    have hk : (2 : ZMod p)⁻¹ • ((e k - e l) + (e k + e l)) = e k := by
      rw [show (e k - e l) + (e k + e l) = (2 : ZMod p) • e k by
        rw [two_smul]; abel,
        smul_smul, inv_mul_cancel₀ h2, one_smul]
    have h1 := cz_form_t_image hd hp2 hN hroot1 v
    have h2' := cz_form_t_image hd hp2 hN hroot2 v
    have hlam1 : czLambda φ t (e k - e l) = czLambda φ t (e a - e b) :=
      cz_lambda_eq_ref hd hp2 hm hN hab hroot1
    have hlam2 : czLambda φ t (e k + e l) = czLambda φ t (e a - e b) :=
      cz_lambda_eq_ref hd hp2 hm hN hab hroot2
    have hEk : ggCZForm φ (t v) (t (e k)) =
        (2 : ZMod p)⁻¹ * (ggCZForm φ (t v) (t (e k - e l)) +
          ggCZForm φ (t v) (t (e k + e l))) := by
      have hdecomp : e k = (2 : ZMod p)⁻¹ • ((e k - e l) + (e k + e l)) := hk.symm
      have hstep : ggCZForm φ (t v) (t (e k)) =
          ggCZForm φ (t v) (t ((2 : ZMod p)⁻¹ • ((e k - e l) + (e k + e l)))) :=
        congrArg (fun z => ggCZForm φ (t v) (t z)) hdecomp
      calc ggCZForm φ (t v) (t (e k))
          = ggCZForm φ (t v) (t ((2 : ZMod p)⁻¹ • ((e k - e l) + (e k + e l)))) :=
              hstep
        _ = ggCZForm φ (t v) ((2 : ZMod p)⁻¹ • t ((e k - e l) + (e k + e l))) := by
              rw [map_smul]
        _ = (2 : ZMod p)⁻¹ * ggCZForm φ (t v) (t ((e k - e l) + (e k + e l))) := by
              rw [ggCZForm_smul_right]
        _ = (2 : ZMod p)⁻¹ * (ggCZForm φ (t v) (t (e k - e l)) +
              ggCZForm φ (t v) (t (e k + e l))) := by
              rw [map_add, ggCZForm_add_right]
    have hVk : ggCZForm φ v (e k) =
        (2 : ZMod p)⁻¹ * (ggCZForm φ v (e k - e l) +
          ggCZForm φ v (e k + e l)) := by
      have hdecomp : e k = (2 : ZMod p)⁻¹ • ((e k - e l) + (e k + e l)) := hk.symm
      have hstep : ggCZForm φ v (e k) =
          ggCZForm φ v ((2 : ZMod p)⁻¹ • ((e k - e l) + (e k + e l))) :=
        congrArg (fun z => ggCZForm φ v z) hdecomp
      calc ggCZForm φ v (e k)
          = ggCZForm φ v ((2 : ZMod p)⁻¹ • ((e k - e l) + (e k + e l))) := hstep
        _ = (2 : ZMod p)⁻¹ * ggCZForm φ v ((e k - e l) + (e k + e l)) := by
              rw [ggCZForm_smul_right]
        _ = (2 : ZMod p)⁻¹ * (ggCZForm φ v (e k - e l) +
              ggCZForm φ v (e k + e l)) := by
              rw [ggCZForm_add_right]
    change ggCZForm φ (t v) (t (e k)) =
      czLambda φ t (e a - e b) * ggCZForm φ v (e k)
    rw [hEk, hVk, h1, h2', hlam1, hlam2]
    ring
  have hle : czSpan e φ ≤ czRel φ t (czLambda φ t (e a - e b)) v :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hmem)
  exact hle hu

private theorem cz_form_t_all {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (hp2 : p ≠ 2) (hm : 3 ≤ m) {t : V ≃ₗ[ZMod p] V}
    (hC : ∀ v, (∀ k, φ k v = 0) → t v = v)
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ) {a b : Fin m} (hab : a ≠ b) :
    ∀ v w, ggCZForm φ (t v) (t w) = czLambda φ t (e a - e b) * ggCZForm φ v w := by
  intro v w
  set lam := czLambda φ t (e a - e b) with hlam
  set y := czProj e φ w with hy
  have hsplit : w = y + (w - y) := by abel
  have hcφ : ∀ k, φ k (w - y) = 0 := by
    intro k
    rw [map_sub, czProj_φ hd k w]
    exact sub_self _
  have hfix : t (w - y) = w - y := hC _ hcφ
  have hspan : y ∈ czSpan e φ := by
    rw [hy]
    exact czProj_mem_span w
  have hrel : ggCZForm φ (t v) (t y) = lam * ggCZForm φ v y :=
    cz_form_t_span hd hp2 hm hN hab hspan
  have hz1 : ggCZForm φ (t v) (t (w - y)) = 0 := by
    rw [hfix, ggCZForm]
    simp [hcφ]
  have hz2 : ggCZForm φ v (w - y) = 0 := by
    simp [ggCZForm, hcφ]
  rw [hsplit, map_add, ggCZForm_add_right, hrel, hz1, ggCZForm_add_right, hz2]
  ring

private theorem cz_exists_e_of_ne_zero {e : Fin m → V}
    {φ : Fin m → Module.Dual (ZMod p) V} (hd : GGCZDual e φ)
    {f : Module.Dual (ZMod p) V}
    (hfC : ∀ c : V, (∀ k, φ k c = 0) → f c = 0) (hf0 : f ≠ 0) :
    ∃ i : Fin m, f (e i) ≠ 0 := by
  by_contra h
  push Not at h
  refine hf0 ?_
  ext v
  set y := czProj e φ v with hy
  have hcφ : ∀ k, φ k (v - y) = 0 := by
    intro k
    rw [map_sub, czProj_φ hd k v]
    exact sub_self _
  have hfy : f y = 0 := by
    rw [hy, czProj_apply, map_sum]
    simp only [LinearMap.map_smul, smul_eq_mul]
    simp [h]
  have hfc : f (v - y) = 0 := hfC _ hcφ
  calc f v = f (y + (v - y)) := congrArg f (by abel)
    _ = f y + f (v - y) := by rw [map_add]
    _ = 0 := by rw [hfy, hfc, add_zero]

private theorem cz_lambda_eq_one {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (hp2 : p ≠ 2) (hm : 3 ≤ m) {t : V ≃ₗ[ZMod p] V}
    (ht : GGLinRefl t) (hC : ∀ v, (∀ k, φ k v = 0) → t v = v)
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ) {a b : Fin m} (hab : a ≠ b) :
    czLambda φ t (e a - e b) = 1 := by
  set lam := czLambda φ t (e a - e b) with hlam
  have hrel : ∀ v w, ggCZForm φ (t v) (t w) = lam * ggCZForm φ v w :=
    cz_form_t_all hd hp2 hm hC hN hab
  obtain ⟨x, f, hfx, htform⟩ := (ggDepA_linRefl_iff hp2 t).mp ht
  obtain ⟨hx0, hf0⟩ := ne_zero_of_apply_eq_two hp2 hfx
  have hfC : ∀ c : V, (∀ k, φ k c = 0) → f c = 0 := by
    intro c hc
    have h1 : t c = c := hC c hc
    rw [htform c] at h1
    have h2 : f c • x = 0 := by
      have h3 : c - f c • x = c - 0 := by simpa using h1
      exact sub_right_inj.mp h3
    exact (smul_eq_zero.mp h2).resolve_right hx0
  by_contra hlam1
  have hBker : ∀ w v : V, f w = 0 → f v = 0 → ggCZForm φ w v = 0 := by
    intro w v hw hv
    have htw : t w = w := by rw [htform w, hw, zero_smul, sub_zero]
    have htv : t v = v := by rw [htform v, hv, zero_smul, sub_zero]
    have h := hrel w v
    rw [htw, htv] at h
    have h1 : (1 - lam) * ggCZForm φ w v = 0 := by
      rw [sub_mul, one_mul, ← h, sub_self]
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr (Ne.symm hlam1))
  obtain ⟨i, hi⟩ := cz_exists_e_of_ne_zero hd hfC hf0
  obtain ⟨j, k, hji, hki, hjk⟩ := cz_exists_two_ne hm i
  let A : ZMod p := f (e i)
  let Bj : ZMod p := f (e j)
  let Bk : ZMod p := f (e k)
  let ui : V := A • e j - Bj • e i
  let uk : V := A • e k - Bk • e i
  have hui : f ui = 0 := by
    change f (A • e j - Bj • e i) = 0
    rw [map_sub, LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
    change A * Bj - Bj * A = 0
    ring
  have huk : f uk = 0 := by
    change f (A • e k - Bk • e i) = 0
    rw [map_sub, LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
    change A * Bk - Bk * A = 0
    ring
  have hBjk : ggCZForm φ ui uk = 0 := hBker ui uk hui huk
  have hBjj : ggCZForm φ ui ui = 0 := hBker ui ui hui hui
  have hBkk : ggCZForm φ uk uk = 0 := hBker uk uk huk huk
  have hBjk' : ggCZForm φ ui uk = Bj * Bk := by
    change ggCZForm φ (A • e j - Bj • e i) (A • e k - Bk • e i) = Bj * Bk
    rw [cz_form_two_roots hd]
    simp [hji, Ne.symm hki, hjk]
  have hBjj' : ggCZForm φ ui ui = A * A + Bj * Bj := by
    change ggCZForm φ (A • e j - Bj • e i) (A • e j - Bj • e i) = A * A + Bj * Bj
    rw [cz_form_two_roots hd]
    simp [hji, Ne.symm hji]
  have hBkk' : ggCZForm φ uk uk = A * A + Bk * Bk := by
    change ggCZForm φ (A • e k - Bk • e i) (A • e k - Bk • e i) = A * A + Bk * Bk
    rw [cz_form_two_roots hd]
    simp [hki, Ne.symm hki]
  rw [hBjk'] at hBjk
  have hzero : Bj * Bk = 0 := hBjk
  rcases mul_eq_zero.mp hzero with hBj | hBk
  · have hA : A * A = 0 := by
      rw [hBjj', hBj] at hBjj
      simpa using hBjj
    have hA' : f (e i) * f (e i) = 0 := hA
    rcases mul_eq_zero.mp hA' with h | h
    · exact hi h
    · exact hi h
  · have hA : A * A = 0 := by
      rw [hBkk', hBk] at hBkk
      simpa using hBkk
    have hA' : f (e i) * f (e i) = 0 := hA
    rcases mul_eq_zero.mp hA' with h | h
    · exact hi h
    · exact hi h

theorem ggCZ_isom_of_normalizes [Finite V] (hp2 : p ≠ 2) (hm : 3 ≤ m) {e : Fin m → V}
    {φ : Fin m → Module.Dual (ZMod p) V} (hd : GGCZDual e φ) {t : V ≃ₗ[ZMod p] V}
    (ht : GGLinRefl t) (hC : ∀ v, (∀ k, φ k v = 0) → t v = v)
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ) :
    (∀ i, t (e i) = ∑ k, φ k (t (e i)) • e k) ∧
      ∀ v w, ggCZForm φ (t v) (t w) = ggCZForm φ v w := by
  obtain ⟨a, b, hab⟩ := cz_exists_pair (by omega : 2 ≤ m)
  have hrel := cz_form_t_all hd hp2 hm hC hN hab
  have hlam := cz_lambda_eq_one hd hp2 hm ht hC hN hab
  refine ⟨?_, ?_⟩
  · intro i
    obtain ⟨j, hji⟩ := cz_exists_ne (by omega : 2 ≤ m) i
    have hroot1 : czIsRoot e φ (e i - e j) :=
      ⟨i, j, hji.symm, 1, Or.inl rfl, by simp⟩
    have hroot2 : czIsRoot e φ (e i + e j) := by
      refine ⟨i, j, hji.symm, -1, Or.inr rfl, ?_⟩
      rw [neg_smul, one_smul, sub_neg_eq_add]
    have h1 : t (e i - e j) ∈ czCoord e φ := czCoord_image_root hd hp2 hN hroot1
    have h2 : t (e i + e j) ∈ czCoord e φ := czCoord_image_root hd hp2 hN hroot2
    have hk : (2 : ZMod p)⁻¹ • ((e i - e j) + (e i + e j)) = e i := by
      rw [show (e i - e j) + (e i + e j) = (2 : ZMod p) • e i by
        rw [two_smul]; abel,
        smul_smul, inv_mul_cancel₀ (zmod_two_ne_zero hp2), one_smul]
    have hsum : t (e i) = (2 : ZMod p)⁻¹ • (t (e i - e j) + t (e i + e j)) := by
      have hsplit : e i = (2 : ZMod p)⁻¹ • ((e i - e j) + (e i + e j)) := hk.symm
      calc t (e i) = t ((2 : ZMod p)⁻¹ • ((e i - e j) + (e i + e j))) :=
            congrArg t hsplit
        _ = (2 : ZMod p)⁻¹ • t ((e i - e j) + (e i + e j)) := by rw [map_smul]
        _ = (2 : ZMod p)⁻¹ • (t (e i - e j) + t (e i + e j)) := by rw [map_add]
    have hmem : t (e i) ∈ czCoord e φ := by
      rw [hsum]
      exact (czCoord e φ).smul_mem _ ((czCoord e φ).add_mem h1 h2)
    rw [czCoord_mem_iff, czProj_apply] at hmem
    exact hmem.symm
  · intro v w
    rw [hrel v w, hlam, one_mul]

end

end CFSG.StandardType

end
