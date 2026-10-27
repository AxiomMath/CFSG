module

public import CFSG.RankThree.PartOne.CTP.SeitzSpClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81.PSpOuter

open Subgroup Matrix CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.Classical (spForm spEnd spEnd_apply spForm_isAlt spForm_nondegenerate)
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull

section LinearAlgebra

variable {F : Type} [Field F]

private lemma spForm_swap {r : ℕ} (x y : Fin r ⊕ Fin r → F) :
    spForm r F y x = -spForm r F x y := by
  rw [← spForm_isAlt.neg_eq]

private lemma spForm_sub_smul {r : ℕ} {u a b : Fin r ⊕ Fin r → F} {s t : F} :
    spForm r F u (s • a - t • b) =
      s * spForm r F u a - t * spForm r F u b := by
  rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

private lemma X_eig_plus {V : Type*} [AddCommGroup V] [Module F V]
    {X : Module.End F V} {lam : F} (hXX : ∀ y, X (X y) = (lam * lam) • y) (z : V) :
    X (X z + lam • z) = lam • (X z + lam • z) := by
  rw [map_add, map_smul, hXX]
  module

private lemma X_eig_minus {V : Type*} [AddCommGroup V] [Module F V]
    {X : Module.End F V} {lam : F} (hXX : ∀ y, X (X y) = (lam * lam) • y) (z : V) :
    X (lam • z - X z) = -lam • (lam • z - X z) := by
  rw [map_sub, map_smul, hXX]
  module

private lemma X_eig_smul {V : Type*} [AddCommGroup V] [Module F V]
    {X : Module.End F V} {mu : F} {c : F} {w : V} (hw : X w = mu • w) :
    X (c • w) = mu • (c • w) := by
  rw [map_smul, hw]
  module

private lemma X_sub_smul {V : Type*} [AddCommGroup V] [Module F V]
    {X : Module.End F V} {c : F} {a b : V} {s t : F}
    (ha : X a = c • a) (hb : X b = c • b) :
    X (s • a - t • b) = c • (s • a - t • b) := by
  rw [map_sub, map_smul, map_smul, ha, hb]
  module

private lemma plus_add_minus {V : Type*} [AddCommGroup V] [Module F V]
    {X : Module.End F V} {lam : F} (h2 : (2 : F) ≠ 0) (hlam : lam ≠ 0) (z : V) :
    (2 * lam)⁻¹ • (X z + lam • z) + (2 * lam)⁻¹ • (lam • z - X z) = z := by
  rw [← smul_add]
  have hinner : (X z + lam • z) + (lam • z - X z) = (2 * lam) • z := by
    module
  rw [hinner, smul_smul, inv_mul_cancel₀ (mul_ne_zero h2 hlam), one_smul]

private lemma minus_self {V : Type*} [AddCommGroup V] [Module F V]
    {X : Module.End F V} {lam : F} (h2 : (2 : F) ≠ 0) (hlam : lam ≠ 0) {z : V}
    (hz : X z = -lam • z) :
    (2 * lam)⁻¹ • (lam • z - X z) = z := by
  have hinner : lam • z - X z = (2 * lam) • z := by
    rw [hz, neg_smul, sub_neg_eq_add]
    module
  rw [hinner, smul_smul, inv_mul_cancel₀ (mul_ne_zero h2 hlam), one_smul]

end LinearAlgebra

section LeviVec

variable {F : Type} [Field F]

theorem form_eq_zero_of_skew_eig {r : ℕ} (h2 : (2 : F) ≠ 0)
    {X : Module.End F (Fin r ⊕ Fin r → F)}
    (hXadj : ∀ y z, spForm r F (X y) z = -spForm r F y (X z)) {lam : F} (hlam : lam ≠ 0)
    {x y : Fin r ⊕ Fin r → F} (hx : X x = lam • x) (hy : X y = lam • y) :
    spForm r F x y = 0 := by
  have h1 : spForm r F (X x) y = lam * spForm r F x y := by
    rw [hx]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have h2' : spForm r F (X x) y = -(lam * spForm r F x y) := by
    rw [hXadj, hy]
    simp only [map_smul, smul_eq_mul]
  have hL : lam * spForm r F x y = -(lam * spForm r F x y) := h1.symm.trans h2'
  have hzero : (2 : F) * (lam * spForm r F x y) = 0 := by
    rw [two_mul]
    nth_rewrite 2 [hL]
    exact add_neg_cancel _
  have h3 : lam * spForm r F x y = 0 := (mul_eq_zero.mp hzero).resolve_left h2
  exact (mul_eq_zero.mp h3).resolve_left hlam

theorem exists_orth_eig (h2 : (2 : F) ≠ 0) {X Y : Module.End F (Fin 2 ⊕ Fin 2 → F)}
    {lam μ : F} (hlam : lam ≠ 0) (hXX : ∀ y, X (X y) = (lam * lam) • y)
    (hμ : μ ≠ 0) (hYY : ∀ y, Y (Y y) = -μ • y) (hXY : ∀ y, X (Y y) = -Y (X y))
    {u : Fin 2 ⊕ Fin 2 → F} (hu : X u = lam • u) (huY : spForm 2 F u (Y u) ≠ 0) :
    ∃ v, v ≠ 0 ∧ X v = -lam • v ∧ spForm 2 F u v = 0 := by
  classical
  let k : F := spForm 2 F u (Y u)
  have hk : k ≠ 0 := huY
  let plus : (Fin 2 ⊕ Fin 2 → F) → (Fin 2 ⊕ Fin 2 → F) :=
    fun z => (2 * lam)⁻¹ • (X z + lam • z)
  let minus : (Fin 2 ⊕ Fin 2 → F) → (Fin 2 ⊕ Fin 2 → F) :=
    fun z => (2 * lam)⁻¹ • (lam • z - X z)
  have hXplus : ∀ z, X (plus z) = lam • plus z := fun z =>
    X_eig_smul (X_eig_plus hXX z)
  have hXminus : ∀ z, X (minus z) = -lam • minus z := fun z =>
    X_eig_smul (X_eig_minus hXX z)
  have hplus_minus : ∀ z, plus z + minus z = z := fun z =>
    plus_add_minus h2 hlam z
  have hminus_self : ∀ z, X z = -lam • z → minus z = z := fun z hz =>
    minus_self h2 hlam hz
  have hXYu : X (Y u) = -lam • Y u := by
    rw [hXY, hu]
    simp only [map_smul, neg_smul]
  by_contra hno
  have hzero : ∀ v, X v = -lam • v → spForm 2 F u v = 0 → v = 0 := by
    intro v hv hb
    by_contra hne
    exact hno ⟨v, hne, hv, hb⟩
  have hmem : ∀ z, minus z ∈ Submodule.span F ({Y u} : Set (Fin 2 ⊕ Fin 2 → F)) := by
    intro z
    have hv_eig : X (k • minus z - spForm 2 F u (minus z) • Y u) =
        -lam • (k • minus z - spForm 2 F u (minus z) • Y u) :=
      X_sub_smul (hXminus z) hXYu
    have hv_orth :
        spForm 2 F u (k • minus z - spForm 2 F u (minus z) • Y u) = 0 := by
      rw [spForm_sub_smul]
      have hkval : spForm 2 F u (Y u) = k := rfl
      rw [hkval]
      ring
    have hvzero := hzero _ hv_eig hv_orth
    have hsub : k • minus z = spForm 2 F u (minus z) • Y u := sub_eq_zero.mp hvzero
    refine Submodule.mem_span_singleton.mpr ⟨k⁻¹ * spForm 2 F u (minus z), ?_⟩
    calc
      (k⁻¹ * spForm 2 F u (minus z)) • Y u =
          k⁻¹ • (spForm 2 F u (minus z) • Y u) := by rw [smul_smul]
      _ = k⁻¹ • (k • minus z) := by rw [← hsub]
      _ = minus z := by rw [smul_smul, inv_mul_cancel₀ hk, one_smul]
  have hplus_mem : ∀ z, plus z ∈ Submodule.span F ({u} : Set (Fin 2 ⊕ Fin 2 → F)) := by
    intro z
    have hY_eig : X (Y (plus z)) = -lam • Y (plus z) := by
      rw [hXY, hXplus z]
      simp only [map_smul, neg_smul]
    have hY_mem : Y (plus z) ∈ Submodule.span F ({Y u} : Set (Fin 2 ⊕ Fin 2 → F)) := by
      rw [← hminus_self (Y (plus z)) hY_eig]
      exact hmem _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hY_mem
    have hY2 : Y (Y (plus z)) = -μ • (c • u) := by
      rw [← hc, map_smul, hYY]
      module
    have hcancel : (-μ) ≠ 0 := neg_ne_zero.mpr hμ
    have hplus_eq : plus z = c • u := by
      have h : (-μ) • plus z = (-μ) • (c • u) := by
        rw [← hYY (plus z), hY2]
      exact (smul_right_inj hcancel).mp h
    exact Submodule.mem_span_singleton.mpr ⟨c, by rw [hplus_eq]⟩
  have hmem_all : ∀ z, z ∈ Submodule.span F ({u, Y u} : Set (Fin 2 ⊕ Fin 2 → F)) := by
    intro z
    have h1 : plus z ∈ Submodule.span F ({u, Y u} : Set (Fin 2 ⊕ Fin 2 → F)) :=
      Submodule.span_mono (Set.singleton_subset_iff.mpr (by simp)) (hplus_mem z)
    have h2 : minus z ∈ Submodule.span F ({u, Y u} : Set (Fin 2 ⊕ Fin 2 → F)) :=
      Submodule.span_mono (Set.singleton_subset_iff.mpr (by simp)) (hmem z)
    rw [← hplus_minus z]
    exact Submodule.add_mem _ h1 h2
  have htop : Submodule.span F ({u, Y u} : Set (Fin 2 ⊕ Fin 2 → F)) = ⊤ :=
    le_antisymm le_top fun z _ => hmem_all z
  have hbound : Module.finrank F (Submodule.span F ({u, Y u} : Set (Fin 2 ⊕ Fin 2 → F))) ≤ 2 := by
    have h := finrank_span_finset_le_card (R := F) ({u, Y u} : Finset (Fin 2 ⊕ Fin 2 → F))
    rw [Finset.coe_insert, Finset.coe_singleton] at h
    exact h.trans (by simpa using Finset.card_le_two)
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card] at hbound
  simp only [Fintype.card_sum, Fintype.card_fin, Nat.reduceAdd] at hbound
  omega

theorem transCenter_of_eig {r : ℕ} (h2 : (2 : F) ≠ 0) {H : Subgroup (StatedSp r F)}
    {X : Module.End F (Fin r ⊕ Fin r → F)}
    (hXadj : ∀ y z, spForm r F (X y) z = -spForm r F y (X z)) {lam : F} (hlam : lam ≠ 0)
    (hXX : ∀ y, X (X y) = (lam * lam) • y)
    (hc : ∀ x, (X x = lam • x ∨ X x = -lam • x) → TransCenter H x) :
    ∀ v, TransCenter H v := by
  intro v
  let plus : (Fin r ⊕ Fin r → F) → (Fin r ⊕ Fin r → F) :=
    fun z => (2 * lam)⁻¹ • (X z + lam • z)
  let minus : (Fin r ⊕ Fin r → F) → (Fin r ⊕ Fin r → F) :=
    fun z => (2 * lam)⁻¹ • (lam • z - X z)
  have hXplus : ∀ z, X (plus z) = lam • plus z := fun z =>
    X_eig_smul (X_eig_plus hXX z)
  have hXminus : ∀ z, X (minus z) = -lam • minus z := fun z =>
    X_eig_smul (X_eig_minus hXX z)
  have hplus_minus : plus v + minus v = v := plus_add_minus h2 hlam v
  have hplus_c : TransCenter H (plus v) := hc (plus v) (Or.inl (hXplus v))
  have hminus_c : TransCenter H (minus v) := hc (minus v) (Or.inr (hXminus v))
  have hiso_lam : ∀ x y, X x = lam • x → X y = lam • y → spForm r F x y = 0 :=
    fun x y hx hy => form_eq_zero_of_skew_eig h2 hXadj hlam hx hy
  have hiso_neg : ∀ x y, X x = -lam • x → X y = -lam • y → spForm r F x y = 0 :=
    fun x y hx hy => form_eq_zero_of_skew_eig h2 hXadj (neg_ne_zero.mpr hlam) hx hy
  by_cases hplus0 : plus v = 0
  · rw [← hplus_minus, hplus0, zero_add]
    exact hminus_c
  by_cases hminus0 : minus v = 0
  · rw [← hplus_minus, hminus0, add_zero]
    exact hplus_c
  by_cases hform_ne : spForm r F (plus v) (minus v) ≠ 0
  · rw [← hplus_minus]
    exact TransCenter.add hplus_c hminus_c hform_ne
  have hform : spForm r F (plus v) (minus v) = 0 := not_not.mp hform_ne
  obtain ⟨y, hy⟩ : ∃ y, spForm r F (minus v) y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hminus0 (spForm_nondegenerate.1 (minus v) hcon)
  let w : Fin r ⊕ Fin r → F := plus y
  let a : Fin r ⊕ Fin r → F := (plus v - w) + minus v
  have hw_eig : X w = lam • w := hXplus y
  have hw_c : TransCenter H w := hc w (Or.inl hw_eig)
  have hb_w : spForm r F (minus v) w = spForm r F (minus v) y := by
    have hydec : plus y + minus y = y := plus_add_minus h2 hlam y
    change spForm r F (minus v) (plus y) = spForm r F (minus v) y
    conv_rhs => rw [← hydec]
    rw [map_add, hiso_neg (minus v) (minus y) (hXminus v) (hXminus y), add_zero]
  have hform_sub : spForm r F (plus v - w) (minus v) ≠ 0 := by
    have hsub : spForm r F (plus v - w) (minus v) = spForm r F (minus v) w := by
      rw [map_sub, LinearMap.sub_apply, hform, zero_sub, spForm_swap w (minus v)]
    rw [hsub, hb_w]
    exact hy
  have hplus_sub_eig : X (plus v - w) = lam • (plus v - w) := by
    rw [map_sub, hXplus v, hw_eig, smul_sub]
  have hsub_c : TransCenter H (plus v - w) := hc (plus v - w) (Or.inl hplus_sub_eig)
  have ha_c : TransCenter H a := TransCenter.add hsub_c hminus_c hform_sub
  have hb_aw : spForm r F a w ≠ 0 := by
    have ha_eq : spForm r F a w = spForm r F (minus v) w := by
      change spForm r F ((plus v - w) + minus v) w = spForm r F (minus v) w
      rw [map_add, LinearMap.add_apply, map_sub, LinearMap.sub_apply,
        hiso_lam (plus v) w (hXplus v) hw_eig, spForm_isAlt.self_eq_zero w, sub_zero, zero_add]
    rw [ha_eq, hb_w]
    exact hy
  have hwa_c : TransCenter H (a + w) := TransCenter.add ha_c hw_c hb_aw
  have hv_eq : v = a + w := by
    rw [← hplus_minus]
    dsimp only [a, w]
    abel
  rw [hv_eq]
  exact hwa_c

end LeviVec

end CFSG.LocalAnalysis.WeakClosure81.PSpOuter
