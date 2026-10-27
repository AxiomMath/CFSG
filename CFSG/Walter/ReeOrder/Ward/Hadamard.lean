module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

open scoped BigOperators

namespace CFSG.Walter.Ward

variable {α : Type*}

theorem sum_sq_g (R : Finset α) (hR : R.card = 4) (w₀ w₁ w₂ : α → ℤ)
    (h0 : ∀ y ∈ R, w₀ y * w₀ y = 1) (h1 : ∀ y ∈ R, w₁ y * w₁ y = 1)
    (h2 : ∀ y ∈ R, w₂ y * w₂ y = 1)
    (s0 : ∑ y ∈ R, w₀ y = 0) (s1 : ∑ y ∈ R, w₁ y = 0) (s2 : ∑ y ∈ R, w₂ y = 0)
    (s01 : ∑ y ∈ R, w₀ y * w₁ y = 0) (s02 : ∑ y ∈ R, w₀ y * w₂ y = 0)
    (s12 : ∑ y ∈ R, w₁ y * w₂ y = 0) (c₀ c₁ c₂ : ℤ) (hc₀ : c₀ * c₀ = 1) (hc₁ : c₁ * c₁ = 1)
    (hc₂ : c₂ * c₂ = 1) :
    ∑ y ∈ R, (1 + c₀ * w₀ y + c₁ * w₁ y + c₂ * w₂ y) ^ 2 = 16 := by
  have hexp : ∀ y ∈ R, (1 + c₀ * w₀ y + c₁ * w₁ y + c₂ * w₂ y) ^ 2 =
      4 + 2 * c₀ * w₀ y + 2 * c₁ * w₁ y + 2 * c₂ * w₂ y + 2 * (c₀ * c₁) * (w₀ y * w₁ y) +
        2 * (c₀ * c₂) * (w₀ y * w₂ y) + 2 * (c₁ * c₂) * (w₁ y * w₂ y) := by
    intro y hy
    have e0 := h0 y hy
    have e1 := h1 y hy
    have e2 := h2 y hy
    linear_combination (c₀ * c₀) * e0 + (c₁ * c₁) * e1 + (c₂ * c₂) * e2 + hc₀ + hc₁ + hc₂
  rw [Finset.sum_congr rfl hexp]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, hR, s0, s1, s2, s01,
    s02, s12, nsmul_eq_mul]
  norm_num

theorem hadamard [DecidableEq α] (R : Finset α) (hR : R.card = 4) (u₀ u₁ u₂ : α → ℤ)
    (h0 : ∀ y ∈ R, u₀ y * u₀ y = 1) (h1 : ∀ y ∈ R, u₁ y * u₁ y = 1)
    (h2 : ∀ y ∈ R, u₂ y * u₂ y = 1)
    (s01 : ∑ y ∈ R, u₀ y * u₁ y = 0) (s02 : ∑ y ∈ R, u₀ y * u₂ y = 0)
    (s12 : ∑ y ∈ R, u₁ y * u₂ y = 0) (f : α → ℤ) (f0 : ∑ y ∈ R, f y * u₀ y = 0)
    (f1 : ∑ y ∈ R, f y * u₁ y = 0) (f2 : ∑ y ∈ R, f y * u₂ y = 0) {x : α} (hx : x ∈ R) :
    4 * (f x * (u₀ x * u₁ x * u₂ x)) = ∑ y ∈ R, f y * (u₀ y * u₁ y * u₂ y) := by
  set w₀ : α → ℤ := fun y => u₁ y * u₂ y with hw₀
  set w₁ : α → ℤ := fun y => u₀ y * u₂ y with hw₁
  set w₂ : α → ℤ := fun y => u₀ y * u₁ y with hw₂
  have hw₀sq : ∀ y ∈ R, w₀ y * w₀ y = 1 := fun y hy => by
    simp only [hw₀]; linear_combination (u₂ y * u₂ y) * h1 y hy + h2 y hy
  have hw₁sq : ∀ y ∈ R, w₁ y * w₁ y = 1 := fun y hy => by
    simp only [hw₁]; linear_combination (u₂ y * u₂ y) * h0 y hy + h2 y hy
  have hw₂sq : ∀ y ∈ R, w₂ y * w₂ y = 1 := fun y hy => by
    simp only [hw₂]; linear_combination (u₁ y * u₁ y) * h0 y hy + h1 y hy
  have hs0 : ∑ y ∈ R, w₀ y = 0 := s12
  have hs1 : ∑ y ∈ R, w₁ y = 0 := s02
  have hs2 : ∑ y ∈ R, w₂ y = 0 := s01
  have hs01 : ∑ y ∈ R, w₀ y * w₁ y = 0 := by
    rw [← s01]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [hw₀, hw₁]
    linear_combination (u₀ y * u₁ y) * h2 y hy
  have hs02 : ∑ y ∈ R, w₀ y * w₂ y = 0 := by
    rw [← s02]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [hw₀, hw₂]
    linear_combination (u₀ y * u₂ y) * h1 y hy
  have hs12 : ∑ y ∈ R, w₁ y * w₂ y = 0 := by
    rw [← s12]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [hw₁, hw₂]
    linear_combination (u₁ y * u₂ y) * h0 y hy
  set g : α → ℤ := fun y => 1 + w₀ x * w₀ y + w₁ x * w₁ y + w₂ x * w₂ y with hg
  have hgx : g x = 4 := by
    simp only [hg]
    have := hw₀sq x hx
    have := hw₁sq x hx
    have := hw₂sq x hx
    linarith
  have hgsq := sum_sq_g R hR w₀ w₁ w₂ hw₀sq hw₁sq hw₂sq hs0 hs1 hs2 hs01 hs02 hs12 (w₀ x) (w₁ x)
    (w₂ x) (hw₀sq x hx) (hw₁sq x hx) (hw₂sq x hx)
  have hg0 : ∀ y ∈ R, y ≠ x → g y = 0 := by
    have hsplit := Finset.add_sum_erase R (fun y => g y ^ 2) hx
    have hgsq' : ∑ y ∈ R, g y ^ 2 = 16 := hgsq
    rw [hgsq', hgx] at hsplit
    have hrest : ∑ y ∈ R.erase x, g y ^ 2 = 0 := by linarith
    intro y hy hyx
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => sq_nonneg (g z))).mp hrest y
      (Finset.mem_erase.mpr ⟨hyx, hy⟩)
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  set a : α → ℤ := fun y => f y * (u₀ y * u₁ y * u₂ y) with ha
  have ha0 : ∑ y ∈ R, a y * w₀ y = 0 := by
    rw [← f0]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [ha, hw₀]
    linear_combination (f y * u₀ y * u₁ y * u₁ y) * h2 y hy + (f y * u₀ y) * h1 y hy
  have ha1 : ∑ y ∈ R, a y * w₁ y = 0 := by
    rw [← f1]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [ha, hw₁]
    linear_combination (f y * u₁ y * u₀ y * u₀ y) * h2 y hy + (f y * u₁ y) * h0 y hy
  have ha2 : ∑ y ∈ R, a y * w₂ y = 0 := by
    rw [← f2]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [ha, hw₂]
    linear_combination (f y * u₂ y * u₀ y * u₀ y) * h1 y hy + (f y * u₂ y) * h0 y hy
  have hag : ∑ y ∈ R, a y * g y = ∑ y ∈ R, a y := by
    have : ∀ y ∈ R, a y * g y = a y + w₀ x * (a y * w₀ y) + w₁ x * (a y * w₁ y) +
        w₂ x * (a y * w₂ y) := fun y _ => by simp only [hg]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ha0, ha1, ha2]
    ring
  have hag' : ∑ y ∈ R, a y * g y = a x * 4 := by
    rw [Finset.sum_eq_single x (fun y hy hyx => by rw [hg0 y hy hyx, mul_zero])
      (fun h => absurd hx h), hgx]
  have := hag.symm.trans hag'
  simp only [ha] at this ⊢
  linarith

end CFSG.Walter.Ward
