module

public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.BetaModels
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

open CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

section Eval

variable {X : Type*} [Group X]

@[simp] theorem evalWord_nil (t : Fin 7 → X) : evalWord t [] = 1 := by simp [evalWord]

theorem evalWord_cons (t : Fin 7 → X) (x : Fin 7 × Bool) (r : List (Fin 7 × Bool)) :
    evalWord t (x :: r) = (if x.2 then t x.1 else (t x.1)⁻¹) * evalWord t r := by
  simp [evalWord]

theorem evalWord_map {Y : Type*} [Group Y] (f : X →* Y) (t : Fin 7 → X)
    (r : List (Fin 7 × Bool)) : f (evalWord t r) = evalWord (fun i => f (t i)) r := by
  induction r with
  | nil => simp
  | cons x r ih =>
    rw [evalWord_cons, evalWord_cons, map_mul, ih]
    cases x.2 <;> simp

theorem evalWord_congr {t t' : Fin 7 → X} {r : List (Fin 7 × Bool)}
    (h : ∀ x ∈ r, t x.1 = t' x.1) : evalWord t r = evalWord t' r := by
  induction r with
  | nil => simp
  | cons x r ih =>
    rw [evalWord_cons, evalWord_cons, h x (List.mem_cons_self), ih fun x' hx' =>
      h x' (List.mem_cons_of_mem _ hx')]

theorem evalWord_mem {t : Fin 7 → X} {S : Subgroup X} {r : List (Fin 7 × Bool)}
    (h : ∀ x ∈ r, t x.1 ∈ S) : evalWord t r ∈ S := by
  induction r with
  | nil => simp [S.one_mem]
  | cons x r ih =>
    rw [evalWord_cons]
    refine S.mul_mem ?_ (ih fun x' hx' => h x' (List.mem_cons_of_mem _ hx'))
    have := h x List.mem_cons_self
    cases hx : x.2
    · simpa using S.inv_mem this
    · simpa using this

theorem evalWord_central {y : X} (hy : ∀ g : X, g * y = y * g) (n : Fin 7 → ℤ)
    (σ τ : Fin 7 → X) (hτ : ∀ i, τ i = y ^ n i * σ i) (r : List (Fin 7 × Bool)) :
    evalWord τ r = y ^ (r.map fun x => if x.2 then n x.1 else - n x.1).sum * evalWord σ r := by
  have hc : ∀ (k : ℤ) (g : X), g * y ^ k = y ^ k * g := fun k g =>
    ((Commute.zpow_right (show Commute g y from hy g) k).eq)
  induction r with
  | nil => simp
  | cons x r ih =>
    rw [evalWord_cons, evalWord_cons, ih, List.map_cons, List.sum_cons]
    obtain ⟨i, b⟩ := x
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, hτ i, mul_inv_rev]
      set S := (r.map fun x => if x.2 then n x.1 else -n x.1).sum with hS
      calc (σ i)⁻¹ * (y ^ n i)⁻¹ * (y ^ S * evalWord σ r)
          = (σ i)⁻¹ * (y ^ (-n i) * y ^ S) * evalWord σ r := by
            rw [← zpow_neg]; simp only [mul_assoc]
        _ = (σ i)⁻¹ * y ^ (-n i + S) * evalWord σ r := by rw [← zpow_add]
        _ = y ^ (-n i + S) * ((σ i)⁻¹ * evalWord σ r) := by
            rw [hc (-n i + S) ((σ i)⁻¹)]; simp only [mul_assoc]
    · simp only [↓reduceIte, hτ i]
      set S := (r.map fun x => if x.2 then n x.1 else -n x.1).sum with hS
      calc y ^ n i * σ i * (y ^ S * evalWord σ r)
          = y ^ n i * (σ i * y ^ S) * evalWord σ r := by simp only [mul_assoc]
        _ = y ^ n i * (y ^ S * σ i) * evalWord σ r := by rw [hc S (σ i)]
        _ = y ^ (n i + S) * (σ i * evalWord σ r) := by rw [zpow_add]; simp only [mul_assoc]

end Eval

theorem d8Rels_letters : ∀ r ∈ d8Rels, ∀ x ∈ r, x.1.val ≤ 3 := by decide +kernel

theorem a2Rels_letters : ∀ r ∈ a2Rels, ∀ x ∈ r, x.1.val ≤ 3 ∨ x.1.val = 6 := by decide +kernel

theorem a2Rels_exponent : ∀ r ∈ a2Rels,
    (3 : ℤ) ∣ (r.map fun x => if x.2 then
        (if x.1 = 0 ∨ x.1 = 6 then (1 : ℤ) else 0) else - (if x.1 = 0 ∨ x.1 = 6 then (1 : ℤ) else 0)).sum := by
  decide +kernel

section D8

variable {X : Type*} [Group X]

theorem comm_of_conj_eq {a b : X} (ha : a * a = 1) (h : a * b * a = b) : a * b = b * a := by
  calc a * b = a * b * a * a := by rw [mul_assoc (a * b) a a, ha, mul_one]
    _ = b * a := by rw [h]

theorem comm_of_rel_eval {y e : X} (he : e * e = 1) (h : y * e * y⁻¹ * e = 1) : e * y = y * e := by
  have h1 : y * e * y⁻¹ = e := by
    have := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_of_mul_eq_one_right he]
  calc e * y = (y * e * y⁻¹) * y := by rw [h1]
    _ = y * e := by group

theorem d8_facts {t : Fin 7 → X} (h : ∀ r ∈ d8Rels, evalWord t r = 1) :
    t 1 * t 1 = 1 ∧ t 2 * t 2 = 1 ∧ t 3 * t 3 = 1 ∧ t 0 * t 0 * t 0 = 1 ∧
      t 1 * t 3 = t 3 * t 1 ∧ t 2 * t 3 = t 3 * t 2 ∧
      t 1 * t 0 = t 0 * t 1 ∧ t 2 * t 0 = t 0 * t 2 ∧ t 3 * t 0 = t 0 * t 3 := by
  have h22 := h [(1, true), (1, true)] (by decide +kernel)
  have h33 := h [(2, true), (2, true)] (by decide +kernel)
  have h44 := h [(3, true), (3, true)] (by decide +kernel)
  have h111 := h [(0, true), (0, true), (0, true)] (by decide +kernel)
  have h24 := h [(1, true), (3, true), (1, true), (3, true)] (by decide +kernel)
  have h13 := h [(0, true), (2, true), (0, false), (2, true)] (by decide +kernel)
  have h12 := h [(0, true), (1, true), (0, false), (1, true)] (by decide +kernel)
  have h14 := h [(0, true), (3, true), (0, false), (3, true)] (by decide +kernel)
  have hR1 := h [(2, true), (1, true), (2, true), (3, true), (1, true)] (by decide +kernel)
  have hR2 := h [(2, true), (1, true), (3, true), (2, true), (1, true)] (by decide +kernel)
  simp only [evalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    ↓reduceIte, Bool.false_eq_true] at h22 h33 h44 h111 h24 h13 h12 h14 hR1 hR2
  have e2 : t 1 * t 1 = 1 := h22
  have e3 : t 2 * t 2 = 1 := h33
  have e4 : t 3 * t 3 = 1 := h44
  have i2 : (t 1)⁻¹ = t 1 := inv_eq_of_mul_eq_one_right e2
  have i3 : (t 2)⁻¹ = t 2 := inv_eq_of_mul_eq_one_right e3
  have i4 : (t 3)⁻¹ = t 3 := inv_eq_of_mul_eq_one_right e4
  have c24 : t 1 * t 3 = t 3 * t 1 := by
    have h' : t 1 * t 3 * t 1 * t 3 = 1 := by simpa [mul_assoc] using h24
    have h'' : t 1 * t 3 * t 1 = (t 3)⁻¹ := eq_inv_of_mul_eq_one_left h'
    rw [i4] at h''
    exact comm_of_conj_eq e2 h''
  have c34 : t 2 * t 3 = t 3 * t 2 := by
    have r1 : t 2 * t 1 * t 2 = t 1 * t 3 := by
      have h' : t 2 * t 1 * t 2 * (t 3 * t 1) = 1 := by simpa [mul_assoc] using hR1
      have h'' := eq_inv_of_mul_eq_one_left h'
      rw [mul_inv_rev, i4, i2] at h''
      rw [h'', c24]
    have r2 : t 2 * t 1 * t 3 * t 2 = t 1 := by
      have h' : t 2 * t 1 * t 3 * t 2 * t 1 = 1 := by simpa [mul_assoc] using hR2
      have h'' := eq_inv_of_mul_eq_one_left h'
      rw [i2] at h''
      exact h''
    have hx : t 1 * (t 3 * (t 2 * t 3 * t 2)) = t 1 * 1 := by
      calc t 1 * (t 3 * (t 2 * t 3 * t 2)) = t 1 * t 3 * (t 2 * t 3 * t 2) := by
            simp only [mul_assoc]
        _ = (t 2 * t 1 * t 2) * (t 2 * t 3 * t 2) := by rw [r1]
        _ = t 2 * t 1 * (t 2 * t 2) * t 3 * t 2 := by simp only [mul_assoc]
        _ = t 2 * t 1 * t 3 * t 2 := by rw [e3, mul_one]
        _ = t 1 := r2
        _ = t 1 * 1 := by rw [mul_one]
    have hx' : t 3 * (t 2 * t 3 * t 2) = 1 := mul_left_cancel hx
    have hx'' : t 2 * t 3 * t 2 = (t 3)⁻¹ := eq_inv_of_mul_eq_one_right hx'
    rw [i4] at hx''
    exact comm_of_conj_eq e3 hx''
  refine ⟨e2, e3, e4, by simpa [mul_assoc] using h111, c24, c34, ?_, ?_, ?_⟩
  · exact comm_of_rel_eval e2 (by simpa [mul_assoc] using h12)
  · exact comm_of_rel_eval e3 (by simpa [mul_assoc] using h13)
  · exact comm_of_rel_eval e4 (by simpa [mul_assoc] using h14)

end D8

end CFSG.Quasithin.Kleidman.ThreeLocal
