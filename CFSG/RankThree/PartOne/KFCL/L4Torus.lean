module

public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.RankThree.PartOne.KFCL.L4

open Matrix
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def torus (p : ℕ) (K : Type) [Field K] : Subgroup (SL(4, K)) where
  carrier := {g | ∃ d : Fin 4 → K, g.1 = diagonal d ∧ ∀ i, d i ^ p = 1}
  mul_mem' := by
    rintro a b ⟨d, hd, hdp⟩ ⟨e, he, hep⟩
    refine ⟨d * e, ?_, fun i => by simp [mul_pow, hdp i, hep i]⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, hd, he, diagonal_mul_diagonal]
    rfl
  one_mem' := ⟨fun _ => 1, by simp, fun _ => one_pow p⟩
  inv_mem' := by
    rintro a ⟨d, hd, hdp⟩
    refine ⟨fun i => ∏ j ∈ Finset.univ.erase i, d j, ?_, fun i => ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_inv, hd, adjugate_diagonal]
    · rw [← Finset.prod_pow]
      exact Finset.prod_eq_one fun j _ => hdp j

theorem mem_torus_iff {p : ℕ} {g : SL(4, K)} :
    g ∈ torus p K ↔ ∃ d : Fin 4 → K, g.1 = diagonal d ∧ ∀ i, d i ^ p = 1 := Iff.rfl

theorem torus_apply_ne {p : ℕ} {g : SL(4, K)} (hg : g ∈ torus p K) {i j : Fin 4} (hij : i ≠ j) :
    g.1 i j = 0 := by
  obtain ⟨d, hd, -⟩ := hg
  rw [hd, diagonal_apply_ne _ hij]

theorem torus_pow_apply {p : ℕ} {g : SL(4, K)} (hg : g ∈ torus p K) (i : Fin 4) :
    g.1 i i ^ p = 1 := by
  obtain ⟨d, hd, hdp⟩ := hg
  rw [hd, diagonal_apply_eq]
  exact hdp i

theorem torus_prod {p : ℕ} {g : SL(4, K)} (hg : g ∈ torus p K) : ∏ i, g.1 i i = 1 := by
  obtain ⟨d, hd, -⟩ := hg
  have h1 := g.2
  rw [hd, det_diagonal] at h1
  simpa [hd] using h1

theorem torus_diag_ne {p : ℕ} {g : SL(4, K)} (hg : g ∈ torus p K) (i : Fin 4) : g.1 i i ≠ 0 := by
  intro h0
  have := torus_prod hg
  rw [Finset.prod_eq_zero (f := fun j => g.1 j j) (Finset.mem_univ i) h0] at this
  exact zero_ne_one this

theorem torus_mul_apply {p : ℕ} {g h : SL(4, K)} (hg : g ∈ torus p K) (hh : h ∈ torus p K) (i : Fin 4) :
    (g * h).1 i i = g.1 i i * h.1 i i := by
  obtain ⟨d, hd, -⟩ := hg
  obtain ⟨e, he, -⟩ := hh
  rw [Matrix.SpecialLinearGroup.coe_mul, hd, he, diagonal_mul_diagonal]
  simp

theorem torus_inv_apply {p : ℕ} {g : SL(4, K)} (hg : g ∈ torus p K) (i : Fin 4) :
    (g⁻¹).1 i i = (g.1 i i)⁻¹ := by
  have h1 : g.1 i i * (g⁻¹).1 i i = 1 := by
    rw [← torus_mul_apply hg ((torus p K).inv_mem hg) i, mul_inv_cancel]
    simp
  exact eq_inv_of_mul_eq_one_right h1

@[expose] def hypSub (p : ℕ) (K : Type) [Field K] (s : Finset (Fin 4)) : Subgroup (SL(4, K)) where
  carrier := {g | g ∈ torus p K ∧ ∀ a ∈ s, ∀ b ∈ s, g.1 a a = g.1 b b}
  mul_mem' := by
    rintro a b ⟨ha, hai⟩ ⟨hb, hbi⟩
    refine ⟨(torus p K).mul_mem ha hb, fun x hx y hy => ?_⟩
    rw [torus_mul_apply ha hb, torus_mul_apply ha hb, hai x hx y hy, hbi x hx y hy]
  one_mem' := ⟨(torus p K).one_mem, fun x _ y _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, hai⟩
    refine ⟨(torus p K).inv_mem ha, fun x hx y hy => ?_⟩
    rw [torus_inv_apply ha, torus_inv_apply ha, hai x hx y hy]

theorem mem_hypSub_iff {p : ℕ} {s : Finset (Fin 4)} {g : SL(4, K)} :
    g ∈ hypSub p K s ↔ g ∈ torus p K ∧ ∀ a ∈ s, ∀ b ∈ s, g.1 a a = g.1 b b := Iff.rfl

theorem hypSub_le_torus (p : ℕ) (s : Finset (Fin 4)) : hypSub p K s ≤ torus p K := fun _ h => h.1

section Witness

@[expose] def mkTorus (x : Fin 4 → K) (hprod : ∏ i, x i = 1) : SL(4, K) :=
  ⟨diagonal x, by rw [det_diagonal]; exact hprod⟩

theorem mkTorus_apply (x : Fin 4 → K) (h : ∏ i, x i = 1) (a : Fin 4) :
    (mkTorus x h).1 a a = x a := by
  simp [mkTorus]

theorem mkTorus_mem {p : ℕ} {x : Fin 4 → K} (h : ∏ i, x i = 1) (hx : ∀ i, x i ^ p = 1) :
    mkTorus x h ∈ torus p K := ⟨x, rfl, hx⟩

theorem prod_chi {ζ : K} (hζ : ζ ≠ 0) {s : Finset (Fin 4)} (hs : s.card = 2) :
    ∏ k, (if k ∈ s then ζ else ζ⁻¹) = 1 := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h1 : (Finset.univ.filter (fun k => k ∈ s)).card = 2 := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact hs
  have h2 : (Finset.univ.filter (fun k => ¬ k ∈ s)).card = 2 := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 4))) (fun k => k ∈ s)
    rw [h1, Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [h1, h2]
  field_simp

theorem prod_tau {ζ : K} (hζ : ζ ≠ 0) {i j : Fin 4} (hij : i ≠ j) :
    ∏ k, (if k = i then ζ else if k = j then ζ⁻¹ else 1) = 1 := by
  rw [Finset.prod_eq_mul i j hij]
  · simp [hij.symm, hζ]
  · intro c _ hc
    simp [hc.1, hc.2]
  · simp
  · simp

variable {p : ℕ} {ζ : K}

theorem chi_mem_hypSub (hζp : ζ ^ p = 1) (hζ : ζ ≠ 0) {s : Finset (Fin 4)} (hs : s.card = 2) :
    mkTorus (fun k => if k ∈ s then ζ else ζ⁻¹) (prod_chi hζ hs) ∈ hypSub p K s := by
  refine ⟨mkTorus_mem _ fun i => ?_, fun a ha b hb => ?_⟩
  · by_cases hi : i ∈ s
    · simp [hi, hζp]
    · simp [hi, inv_pow, hζp]
  · rw [mkTorus_apply, mkTorus_apply]
    simp [ha, hb]

theorem tau_mem_torus (hζp : ζ ^ p = 1) (hζ : ζ ≠ 0) {i j : Fin 4} (hij : i ≠ j) :
    mkTorus (fun k => if k = i then ζ else if k = j then ζ⁻¹ else 1) (prod_tau hζ hij) ∈ torus p K := by
  refine mkTorus_mem _ fun k => ?_
  by_cases hk : k = i
  · simp [hk, hζp]
  · by_cases hk' : k = j
    · simp [hk', inv_pow, hζp]
    · simp [hk, hk']

theorem tau_not_mem_hypSub (hζ : ζ ≠ 0) (hζ2 : ζ ≠ ζ⁻¹) {i j : Fin 4} (hij : i ≠ j) :
    mkTorus (fun k => if k = i then ζ else if k = j then ζ⁻¹ else 1) (prod_tau hζ hij) ∉
      hypSub p K {i, j} := by
  rintro ⟨-, h⟩
  have := h i (by simp) j (by simp)
  rw [mkTorus_apply, mkTorus_apply] at this
  simp [hij.symm] at this
  exact hζ2 this

theorem hypSub_ne_torus (hζp : ζ ^ p = 1) (hζ : ζ ≠ 0) (hζ2 : ζ ≠ ζ⁻¹) {s : Finset (Fin 4)}
    (hs : s.card = 2) : hypSub p K s ≠ torus p K := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 hs
  intro h
  exact tau_not_mem_hypSub hζ hζ2 hij (h ▸ tau_mem_torus hζp hζ hij)

theorem hypSub_inj (hζp : ζ ^ p = 1) (hζ : ζ ≠ 0) (hζ2 : ζ ≠ ζ⁻¹) {s s' : Finset (Fin 4)}
    (hs : s.card = 2) (hs' : s'.card = 2) (h : hypSub p K s = hypSub p K s') : s = s' := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 hs
  have hchi := chi_mem_hypSub (p := p) hζp hζ hs
  rw [h] at hchi
  have h1 : ∀ a ∈ s', ∀ b ∈ s', (a ∈ ({i, j} : Finset (Fin 4)) ↔ b ∈ ({i, j} : Finset (Fin 4))) := by
    intro a ha b hb
    have := hchi.2 a ha b hb
    rw [mkTorus_apply, mkTorus_apply] at this
    by_cases hA : a ∈ ({i, j} : Finset (Fin 4)) <;> by_cases hB : b ∈ ({i, j} : Finset (Fin 4))
    · simp [hA, hB]
    · simp only [hA, hB, ite_true, ite_false] at this
      exact absurd this hζ2
    · simp only [hA, hB, ite_true, ite_false] at this
      exact absurd this.symm hζ2
    · simp [hA, hB]
  have htau : mkTorus (fun k => if k = i then ζ else if k = j then ζ⁻¹ else 1) (prod_tau hζ hij) ∉
      hypSub p K s' := by
    rw [← h]
    exact tau_not_mem_hypSub hζ hζ2 hij
  have hmeet : ∃ a ∈ s', a ∈ ({i, j} : Finset (Fin 4)) := by
    by_contra hcon
    push Not at hcon
    apply htau
    refine ⟨tau_mem_torus hζp hζ hij, fun a ha b hb => ?_⟩
    rw [mkTorus_apply, mkTorus_apply]
    have ha' := hcon a ha
    have hb' := hcon b hb
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha' hb'
    simp [ha'.1, ha'.2, hb'.1, hb'.2]
  obtain ⟨a₀, ha₀, ha₀s⟩ := hmeet
  have hsub : s' ⊆ {i, j} := fun b hb => (h1 a₀ ha₀ b hb).1 ha₀s
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hs, hs'])).symm

end Witness

end CFSG.RankThree.PartOne.KFCL.L4
