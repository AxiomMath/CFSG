module

public import CFSG.Sporadic.SchreierLemmas.MooreCosets
import Mathlib.Tactic.Group

public section

namespace CFSG.Sporadic.SchreierLemmas

variable {G : Type*} [Group G]

@[expose] def mooreOfChain (s : ℕ → G) (j : ℕ) : G := if j = 1 then s 0 * s 1 else s 0 * s j

theorem sq_of_comm {x y : G} (hx : x * x = 1) (hy : y * y = 1) (h : x * y = y * x) :
    (x * y) ^ 2 = 1 := by
  rw [pow_two]
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [h]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hx, hy, one_mul]

theorem moore_of_chain {D : Set G} (hsq : ∀ x ∈ D, x * x = 1)
    (hcube : ∀ x ∈ D, ∀ y ∈ D, x * y ≠ y * x → (x * y) ^ 3 = 1)
    (hconj : ∀ x ∈ D, ∀ y ∈ D, y * x * y⁻¹ ∈ D) {n : ℕ} (hn : 2 ≤ n) (s : ℕ → G)
    (hs : ∀ i < n, s i ∈ D)
    (hnc : ∀ i, i + 1 < n → s i * s (i + 1) ≠ s (i + 1) * s i)
    (hc : ∀ i j, i + 2 ≤ j → j < n → s i * s j = s j * s i) :
    IsMooreFamily (n - 1) (mooreOfChain s) := by
  have m1 : mooreOfChain s 1 = s 0 * s 1 := by simp [mooreOfChain]
  have mj : ∀ j, j ≠ 1 → mooreOfChain s j = s 0 * s j := fun j hj => by simp [mooreOfChain, hj]
  have hsq' : ∀ i < n, s i * s i = 1 := fun i hi => hsq _ (hs i hi)
  have hinv : ∀ i < n, (s i)⁻¹ = s i := fun i hi => inv_eq_of_mul_eq_one_right (hsq' i hi)
  have hconj0 : ∀ j, 2 ≤ j → j < n → s 0 * s j * s 0 = s j := by
    intro j h2 hj
    rw [hc 0 j (by omega) hj, mul_assoc, hsq' 0 (by omega), mul_one]
  refine ⟨?_, fun j h2 hj => ?_, fun j h2 hj => ?_, fun i j hi hij hj => ?_⟩
  · rw [m1]
    exact hcube _ (hs 0 (by omega)) _ (hs 1 (by omega)) (hnc 0 (by omega))
  · rw [mj j (by omega)]
    exact sq_of_comm (hsq' 0 (by omega)) (hsq' j (by omega)) (hc 0 j (by omega) (by omega))
  · rcases Nat.lt_or_ge j 3 with h3 | h3
    · obtain rfl : j = 2 := by omega
      rw [show 2 - 1 = 1 from rfl, m1, mj 2 (by omega)]
      have ht : s 0 * s 1 * (s 0)⁻¹ ∈ D := hconj _ (hs 1 (by omega)) _ (hs 0 (by omega))
      have e : s 0 * s 1 * (s 0 * s 2) = s 0 * s 1 * (s 0)⁻¹ * s 2 := by
        rw [hinv 0 (by omega)]
        simp only [mul_assoc]
      rw [e]
      refine hcube _ ht _ (hs 2 (by omega)) fun h => hnc 1 (by omega) ?_
      have h02 := hc 0 2 (by omega) (by omega)
      have hs2 : (s 0)⁻¹ * s 2 * s 0 = s 2 := by
        rw [mul_assoc, ← h02, ← mul_assoc, inv_mul_cancel, one_mul]
      have e2 : s 1 * s 2 = (s 0)⁻¹ * (s 0 * s 1 * (s 0)⁻¹ * s 2) * s 0 := by
        calc s 1 * s 2 = s 1 * ((s 0)⁻¹ * s 2 * s 0) := by rw [hs2]
          _ = (s 0)⁻¹ * (s 0 * s 1 * (s 0)⁻¹ * s 2) * s 0 := by group
      have e3 : s 2 * s 1 = (s 0)⁻¹ * (s 2 * (s 0 * s 1 * (s 0)⁻¹)) * s 0 := by
        calc s 2 * s 1 = ((s 0)⁻¹ * s 2 * s 0) * s 1 := by rw [hs2]
          _ = (s 0)⁻¹ * (s 2 * (s 0 * s 1 * (s 0)⁻¹)) * s 0 := by group
      rw [e2, e3, h]
    · rw [mj (j - 1) (by omega), mj j (by omega)]
      have e : s 0 * s (j - 1) * (s 0 * s j) = s (j - 1) * s j := by
        rw [← mul_assoc, hconj0 (j - 1) (by omega) (by omega)]
      rw [e]
      have := hcube _ (hs (j - 1) (by omega)) _ (hs j (by omega))
        (by have := hnc (j - 1) (by omega); rwa [Nat.sub_add_cancel (by omega)] at this)
      exact this
  · rcases Nat.eq_or_lt_of_le hi with rfl | hi2
    · rw [m1, mj j (by omega)]
      have e : s 0 * s 1 * (s 0 * s j) = s 0 * s 1 * (s 0)⁻¹ * s j := by
        rw [hinv 0 (by omega)]
        simp only [mul_assoc]
      rw [e]
      have ht : s 0 * s 1 * (s 0)⁻¹ * (s 0 * s 1 * (s 0)⁻¹) = 1 :=
        hsq _ (hconj _ (hs 1 (by omega)) _ (hs 0 (by omega)))
      refine sq_of_comm ht (hsq' j (by omega)) ?_
      have h0 : Commute (s 0) (s j) := hc 0 j (by omega) (by omega)
      have h1 : Commute (s 1) (s j) := hc 1 j (by omega) (by omega)
      exact ((h0.mul_left h1).mul_left h0.inv_left).eq
    · rw [mj i (by omega), mj j (by omega)]
      have e : s 0 * s i * (s 0 * s j) = s i * s j := by
        rw [← mul_assoc, hconj0 i (by omega) (by omega)]
      rw [e]
      exact sq_of_comm (hsq' i (by omega)) (hsq' j (by omega)) (hc i j hij (by omega))

theorem mooreOfChain_one_ne {s : ℕ → G} (h : s 0 * s 1 ≠ s 1 * s 0) : mooreOfChain s 1 ≠ 1 := by
  intro h1
  simp only [mooreOfChain, if_true] at h1
  apply h
  have : s 1 = (s 0)⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [this, mul_inv_cancel, inv_mul_cancel]

end CFSG.Sporadic.SchreierLemmas

end
