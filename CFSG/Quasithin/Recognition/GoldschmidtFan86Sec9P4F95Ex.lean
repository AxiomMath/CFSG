module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.Fan86

namespace Sec9P4F95Alg

variable {H : Type*} [Group H]

structure LabelTriple (p q r : H) : Prop where
  pq : p * q = q * p
  pr : p * r = r * p
  qr : q * r = r * q
  p2 : p * p = 1
  q2 : q * q = 1
  r2 : r * r = 1
  p1 : p ≠ 1
  q1 : q ≠ 1
  pq' : p ≠ q
  pr' : p ≠ r
  qr' : q ≠ r
  pqr : p * q * r ≠ 1

variable {p q r : H}

theorem eq_of_mul_eq_one' {a b : H} (h : a * b = 1) (hb : b * b = 1) : a = b := by
  rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right hb]

namespace LabelTriple

variable (L : LabelTriple p q r)
include L

theorem pqr_of_eq (h : p = q * r) : False := by
  apply L.pqr
  rw [h]
  calc q * r * q * r = q * (r * q) * r := by group
    _ = q * (q * r) * r := by rw [← L.qr]
    _ = (q * q) * (r * r) := by group
    _ = 1 := by rw [L.q2, L.r2, one_mul]

theorem ex1b {e : ℕ} (he : e < 2) (h : q * r ^ e = p * q * r) : False := by
  interval_cases e
  · simp only [pow_zero, mul_one] at h
    have h2 : q * 1 = q * (p * r) := by
      rw [mul_one]
      calc q = p * q * r := h
        _ = q * p * r := by rw [L.pq]
        _ = q * (p * r) := by group
    exact L.pr' (eq_of_mul_eq_one' (mul_left_cancel h2).symm L.r2)
  · simp only [pow_one] at h
    have h2 : q = p * q := mul_right_cancel h
    have h3 : p * q = 1 * q := by rw [one_mul]; exact h2.symm
    exact L.p1 (mul_right_cancel h3)

theorem ex1c {e : ℕ} (he : e < 2) (h : p * r ^ e = p * q * r) : False := by
  interval_cases e
  · simp only [pow_zero, mul_one] at h
    have h2 : p * 1 = p * (q * r) := by rw [mul_one, ← mul_assoc]; exact h
    exact L.qr' (eq_of_mul_eq_one' (mul_left_cancel h2).symm L.r2)
  · simp only [pow_one] at h
    have h2 : p * r = p * (q * r) := by rw [← mul_assoc]; exact h
    have h3 : 1 * r = q * r := by rw [one_mul]; exact mul_left_cancel h2
    exact L.q1 (mul_right_cancel h3).symm

theorem ex1d (h : r = p * q * r) : False := by
  have h2 : 1 * r = (p * q) * r := by rw [one_mul]; exact h
  exact L.pq' (eq_of_mul_eq_one' (mul_right_cancel h2).symm L.q2)

theorem ex0a {e : ℕ} (he : e < 2) (h : q * p * r ^ e = p) : False := by
  interval_cases e
  · simp only [pow_zero, mul_one] at h
    have h2 : q * p = 1 * p := by rw [one_mul]; exact h
    exact L.q1 (mul_right_cancel h2)
  · simp only [pow_one] at h
    have h2 : p * (q * r) = p * 1 := by
      rw [mul_one]
      calc p * (q * r) = q * p * r := by rw [← mul_assoc, L.pq]
        _ = p := h
    exact L.qr' (eq_of_mul_eq_one' (mul_left_cancel h2) L.r2)

theorem ex0b {e : ℕ} (he : e < 2) (h : q * r ^ e = p) : False := by
  interval_cases e
  · simp only [pow_zero, mul_one] at h
    exact L.pq' h.symm
  · simp only [pow_one] at h
    exact L.pqr_of_eq h.symm

theorem excA {e : ℕ} (he : e < 2) (h : q * p * r ^ e = q * r) : False := by
  interval_cases e
  · simp only [pow_zero, mul_one] at h
    exact L.pr' (mul_left_cancel h)
  · simp only [pow_one] at h
    have h2 : q * p = q := mul_right_cancel h
    have h3 : q * p = q * 1 := by rw [mul_one]; exact h2
    exact L.p1 (mul_left_cancel h3)

theorem excC {e : ℕ} (he : e < 2) (h : p * r ^ e = q * r) : False := by
  interval_cases e
  · simp only [pow_zero, mul_one] at h
    exact L.pqr_of_eq h
  · simp only [pow_one] at h
    exact L.pq' (mul_right_cancel h)

theorem excD (h : r = q * r) : False := by
  have h2 : 1 * r = q * r := by rw [one_mul]; exact h
  exact L.q1 (mul_right_cancel h2).symm

end LabelTriple

end Sec9P4F95Alg

end CFSG.Quasithin.Fan86
