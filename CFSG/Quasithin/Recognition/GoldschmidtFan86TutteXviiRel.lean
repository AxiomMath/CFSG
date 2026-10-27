module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteXviiPset

public section

namespace CFSG.Quasithin.Fan86.Tutte.Xvii

variable {H : Type*} [Group H] {r l : H}

theorem swap_of_sq {x y : H} (hxy : x * y * (x * y) = 1) : x * y * x = y⁻¹ :=
  mul_eq_one_iff_eq_inv.1 (by
    calc x * y * x * y = x * y * (x * y) := by group
      _ = 1 := hxy)

theorem sq_shift {i : ℕ} (hx2 : ∀ k : ℕ, 1 ≤ k → k < i → tx r l k * tx r l k = 1) {k : ℕ}
    (hk1 : 1 ≤ k) (hki : k < i) (j : ℤ) :
    (tx r l j)⁻¹ * tx r l (k + j) * ((tx r l j)⁻¹ * tx r l (k + j)) = 1 := by
  have := conj_sq (hx2 k hk1 hki) (r ^ j)
  rwa [← zpow_neg, shift_x r l k j] at this

variable {i : ℕ} (hx2 : ∀ k : ℕ, 1 ≤ k → k < i → tx r l k * tx r l k = 1)
include hx2

theorem inv_tx {k : ℕ} (hk1 : 1 ≤ k) (hki : k < i) : (tx r l k)⁻¹ = tx r l k :=
  inv_eq_of_mul_eq_one_right (hx2 k hk1 hki)

theorem rel_a {t : ℕ} (ht1 : 1 ≤ t) (hti : t < i) :
    tx r l t * tx r l i * tx r l t = (tx r l i)⁻¹ := by
  have h := sq_shift hx2 (k := i - t) (by omega) (by omega) (t : ℤ)
  have hc : (((i - t : ℕ)) : ℤ) + (t : ℤ) = (i : ℤ) := by omega
  rw [hc, inv_tx hx2 ht1 hti] at h
  exact swap_of_sq h

theorem rel_R1 {m : ℕ} (hm1 : 1 ≤ m) (hmi : m < i) :
    tx r l ((i + m : ℕ) : ℤ) * (tx r l i)⁻¹ * tx r l ((i + m : ℕ) : ℤ) = tx r l i := by
  have h := sq_shift hx2 hm1 hmi (i : ℤ)
  have hc : (m : ℤ) + (i : ℤ) = ((i + m : ℕ) : ℤ) := by push_cast; ring
  rw [hc] at h
  calc tx r l ((i + m : ℕ) : ℤ) * (tx r l i)⁻¹ * tx r l ((i + m : ℕ) : ℤ)
      = tx r l i * ((tx r l i)⁻¹ * tx r l ((i + m : ℕ) : ℤ) *
          ((tx r l i)⁻¹ * tx r l ((i + m : ℕ) : ℤ))) := by group
    _ = tx r l i := by rw [h, mul_one]

theorem rel_R2 {m c : ℕ} (hmc : m < c) (hci : c < i) :
    tx r l c * tx r l ((i + m : ℕ) : ℤ) * tx r l c = (tx r l ((i + m : ℕ) : ℤ))⁻¹ := by
  have hc1 : 1 ≤ c := by omega
  have h := sq_shift hx2 (k := i + m - c) (by omega) (by omega) (c : ℤ)
  have hcc : (((i + m - c : ℕ)) : ℤ) + (c : ℤ) = ((i + m : ℕ) : ℤ) := by omega
  rw [hcc, inv_tx hx2 hc1 hci] at h
  exact swap_of_sq h

theorem rel_R3 {m : ℕ} (hm1 : 1 ≤ m) (hmi : m < i) :
    tx r l m * tx r l ((i + m : ℕ) : ℤ) * (tx r l m * tx r l ((i + m : ℕ) : ℤ)) =
      r ^ (-(m : ℤ)) * (tx r l i * tx r l i) * r ^ (m : ℤ) := by
  have h1 := shift_x r l (i : ℤ) (m : ℤ)
  have hc : (i : ℤ) + (m : ℤ) = ((i + m : ℕ) : ℤ) := by push_cast; ring
  rw [hc, ← inv_tx hx2 hm1 hmi, inv_inv] at h1
  calc tx r l m * tx r l ((i + m : ℕ) : ℤ) * (tx r l m * tx r l ((i + m : ℕ) : ℤ))
      = r ^ (-(m : ℤ)) * tx r l i * r ^ (m : ℤ) * (r ^ (-(m : ℤ)) * tx r l i * r ^ (m : ℤ)) := by
        rw [h1]
    _ = r ^ (-(m : ℤ)) * (tx r l i * tx r l i) * r ^ (m : ℤ) := by group

end CFSG.Quasithin.Fan86.Tutte.Xvii
