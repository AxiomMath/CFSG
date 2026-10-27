module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula

import Mathlib.Tactic.Group

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.InvolutionCounting

variable {G : Type*} [Group G]

theorem eq_two_and_isConj_sq_of_even {z v s : G} {d : ℕ} (hz : z * z = 1) (hv : v * v = 1)
    (hs : IsConj z s)
    (hcomm : ∀ r s : G, IsConj z r → IsConj z s → Even (orderOf (r * s)) → Commute r s)
    (hprod : ∀ r s : G, IsConj z r → IsConj z s → r ≠ s → Commute r s → IsConj z (r * s))
    (hd : orderOf (v * s) = 2 * d) (hd0 : d ≠ 0) (heven : Even d) :
    d = 2 ∧ IsConj z ((v * s) ^ 2) := by
  have hs2 : s * s = 1 := mul_self_eq_one_of_isConj hz hs
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hrD : IsConj z (v * s * v⁻¹) := hs.trans (isConj_iff.mpr ⟨v, rfl⟩)
  have hrs : v * s * v⁻¹ * s = (v * s) ^ 2 := by rw [hvinv, sq, mul_assoc]
  have hord : orderOf ((v * s) ^ 2) = d := by
    rw [orderOf_pow_of_dvd two_ne_zero (hd ▸ dvd_mul_right 2 d), hd,
      Nat.mul_div_cancel_left d two_pos]
  have hrcomm : Commute (v * s * v⁻¹) s := hcomm _ s hrD hs (by rw [hrs, hord]; exact heven)
  have hr2 : v * s * v⁻¹ * (v * s * v⁻¹) = 1 := mul_self_eq_one_of_isConj hz hrD
  have hc4 : (v * s) ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, ← hrs, sq,
      show v * s * v⁻¹ * s * (v * s * v⁻¹ * s) =
        v * s * v⁻¹ * (s * (v * s * v⁻¹)) * s by group,
      ← hrcomm.eq, show v * s * v⁻¹ * (v * s * v⁻¹ * s) * s =
        v * s * v⁻¹ * (v * s * v⁻¹) * (s * s) by group, hr2, hs2, one_mul]
  have hd2 : d = 2 := by
    have hdvd := orderOf_dvd_of_pow_eq_one hc4
    rw [hd] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨k, hk⟩ := heven
    omega
  refine ⟨hd2, ?_⟩
  rw [← hrs]
  refine hprod _ s hrD hs (fun heq => ?_) hrcomm
  have hsq : (v * s) ^ 2 = 1 := by rw [← hrs, heq, hs2]
  have hdvd := orderOf_dvd_of_pow_eq_one hsq
  rw [hd, hd2] at hdvd
  norm_num at hdvd

theorem pow_succ_mul_inv_mul_mul_inv {c v : G} (hpow : ∀ k : ℕ, v * (c ^ k)⁻¹ = c ^ k * v)
    (j : ℕ) : c ^ (j + 1) * (c⁻¹ * v) * (c ^ (j + 1))⁻¹ = c ^ (2 * j + 1) * v := by
  calc c ^ (j + 1) * (c⁻¹ * v) * (c ^ (j + 1))⁻¹ = c ^ (j + 1) * c⁻¹ * (v * (c ^ (j + 1))⁻¹) := by
        group
    _ = c ^ (j + 1) * c⁻¹ * (c ^ (j + 1) * v) := by rw [hpow]
    _ = c ^ (2 * j + 1) * v := by group

theorem isConj_pow_mul_and_commute_of_odd {z v s : G} {d : ℕ} (hz : z * z = 1) (hv : v * v = 1)
    (hs : IsConj z s) (hd : orderOf (v * s) = 2 * d) (hodd : Odd d) :
    IsConj z ((v * s) ^ d * v) ∧ Commute ((v * s) ^ d * v) v := by
  have hs2 : s * s = 1 := mul_self_eq_one_of_isConj hz hs
  have hinv := conj_mul_left_eq_inv hv hs2
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hpow : ∀ k : ℕ, v * ((v * s) ^ k)⁻¹ = (v * s) ^ k * v := by
    intro k
    have h := conj_zpow_eq_inv hinv (-(k : ℤ))
    rw [zpow_neg, zpow_natCast, inv_inv] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hsv : (v * s)⁻¹ * v = s := by
    rw [mul_inv_rev, hvinv, mul_assoc, hv, mul_one, inv_eq_of_mul_eq_one_right hs2]
  have hd0 : d ≠ 0 := by
    obtain ⟨j, hj⟩ := hodd
    omega
  have hcd : Commute v ((v * s) ^ d) :=
    commute_of_mem_zpowers hinv (Subgroup.npow_mem_zpowers _ d)
      (mul_self_eq_one_of_orderOf_eq_two (orderOf_pow_half hd hd0))
  refine ⟨hs.trans (isConj_iff.mpr ⟨(v * s) ^ ((d + 1) / 2), ?_⟩),
    hcd.symm.mul_left (Commute.refl v)⟩
  obtain ⟨j, rfl⟩ := hodd
  rw [show (2 * j + 1 + 1) / 2 = j + 1 by omega, ← pow_succ_mul_inv_mul_mul_inv hpow j, hsv]

end CFSG.ShultStronglyClosedTI.InvolutionCounting
