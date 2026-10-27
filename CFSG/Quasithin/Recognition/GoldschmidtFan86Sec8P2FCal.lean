module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.Quasithin.Fan86

namespace Sec8P2F

variable {G : Type*} [Group G]

theorem conj_mul {g : G} (hg : g * g = 1) (x y : G) :
    g * (x * y) * g = (g * x * g) * (g * y * g) := by
  rw [show (g * x * g) * (g * y * g) = g * x * (g * g) * y * g by simp only [mul_assoc], hg,
    mul_one]
  simp only [mul_assoc]

structure FiveRel (a z : Fin 5 → G) (w : G) : Prop where
  sq_a : ∀ i, a i * a i = 1
  sq_z : ∀ m, z m * z m = 1
  sq_w : w * w = 1
  comm_zz : ∀ m n, z m * z n = z n * z m
  comm_zw : ∀ m, z m * w = w * z m
  conj_same : ∀ i, a i * z i * a i = z i
  conj_ne : ∀ i m, i ≠ m → a i * z m * a i = z m * w
  comm_aw : ∀ i, a i * w = w * a i
  comm_aa : ∀ i j, i ≠ j →
    a i * a j = (z (kstar i j) * z (kstar j i)) * (a j * a i)

namespace FiveRel

variable {a z : Fin 5 → G} {w : G} (hR : FiveRel a z w)
include hR

theorem conj_w (i : Fin 5) : a i * w * a i = w := by
  rw [hR.comm_aw i, mul_assoc, hR.sq_a i, mul_one]

theorem E_A3 : z 0 * z 3 * (z 2 * w * (z 0 * w * w)) = z 3 * z 2 * w := by
  have hAB : Commute (z 0) (z 3) := hR.comm_zz 0 3
  have hAC : Commute (z 0) (z 2) := hR.comm_zz 0 2
  have hAw : Commute (z 0) w := hR.comm_zw 0
  calc z 0 * z 3 * (z 2 * w * (z 0 * w * w)) = z 0 * z 3 * (z 2 * w * z 0) := by
        rw [mul_assoc (z 0) w w, hR.sq_w, mul_one]
    _ = (z 0 * z 3 * z 2) * (w * z 0) := by simp only [mul_assoc]
    _ = (z 0 * z 3 * z 2) * (z 0 * w) := by rw [← hAw.eq]
    _ = (z 0 * (z 3 * z 2)) * z 0 * w := by simp only [mul_assoc]
    _ = ((z 3 * z 2) * z 0) * z 0 * w := by rw [(hAB.mul_right hAC).eq]
    _ = z 3 * z 2 * (z 0 * z 0) * w := by simp only [mul_assoc]
    _ = z 3 * z 2 * w := by rw [hR.sq_z 0, mul_one]

theorem comm_pair : a 2 * a 1 * (a 4 * a 3) = (z 3 * z 2 * w) * (a 1 * a 2 * a 3 * a 4) := by
  have h21 : a 2 * a 1 = (z 0 * z 3) * (a 1 * a 2) := hR.comm_aa 2 1 (by decide)
  have h43 : a 4 * a 3 = (z 2 * z 0) * (a 3 * a 4) := hR.comm_aa 4 3 (by decide)
  have t2 : a 2 * (z 2 * z 0) * a 2 = z 2 * (z 0 * w) := by
    rw [conj_mul (hR.sq_a 2), hR.conj_same 2, hR.conj_ne 2 0 (by decide)]
  have t1 : a 1 * (z 2 * (z 0 * w)) * a 1 = (z 2 * w) * ((z 0 * w) * w) := by
    rw [conj_mul (hR.sq_a 1), conj_mul (hR.sq_a 1), hR.conj_ne 1 2 (by decide),
      hR.conj_ne 1 0 (by decide), hR.conj_w 1]
  have hs : a 1 * a 2 * (z 2 * z 0) = (z 2 * w) * ((z 0 * w) * w) * (a 1 * a 2) := by
    calc a 1 * a 2 * (z 2 * z 0) = a 1 * (a 2 * (z 2 * z 0) * a 2) * a 2 := by
          rw [show a 1 * (a 2 * (z 2 * z 0) * a 2) * a 2 = a 1 * a 2 * (z 2 * z 0) * (a 2 * a 2)
            by simp only [mul_assoc], hR.sq_a 2, mul_one]
      _ = a 1 * (z 2 * (z 0 * w)) * a 2 := by rw [t2]
      _ = (a 1 * (z 2 * (z 0 * w)) * a 1) * (a 1 * a 2) := by
          rw [show (a 1 * (z 2 * (z 0 * w)) * a 1) * (a 1 * a 2) =
            a 1 * (z 2 * (z 0 * w)) * (a 1 * a 1) * a 2 by simp only [mul_assoc], hR.sq_a 1,
            mul_one]
      _ = (z 2 * w) * ((z 0 * w) * w) * (a 1 * a 2) := by rw [t1]
  calc a 2 * a 1 * (a 4 * a 3)
      = (z 0 * z 3) * (a 1 * a 2) * ((z 2 * z 0) * (a 3 * a 4)) := by rw [h21, h43]
    _ = (z 0 * z 3) * (a 1 * a 2 * (z 2 * z 0)) * (a 3 * a 4) := by simp only [mul_assoc]
    _ = (z 0 * z 3) * ((z 2 * w) * ((z 0 * w) * w) * (a 1 * a 2)) * (a 3 * a 4) := by rw [hs]
    _ = (z 0 * z 3 * (z 2 * w * (z 0 * w * w))) * (a 1 * a 2 * a 3 * a 4) := by
          simp only [mul_assoc]
    _ = (z 3 * z 2 * w) * (a 1 * a 2 * a 3 * a 4) := by rw [hR.E_A3]

theorem conj_c : a 0 * (z 3 * z 2 * w) * a 0 = z 3 * z 2 * w := by
  have hBw : Commute (z 3) w := hR.comm_zw 3
  have hCw : Commute (z 2) w := hR.comm_zw 2
  rw [conj_mul (hR.sq_a 0), conj_mul (hR.sq_a 0), hR.conj_ne 0 3 (by decide),
    hR.conj_ne 0 2 (by decide), hR.conj_w 0]
  calc z 3 * w * (z 2 * w) * w = z 3 * (w * z 2) * (w * w) := by simp only [mul_assoc]
    _ = z 3 * z 2 * w := by
        rw [← hCw.eq, hR.sq_w]
        simp only [mul_assoc, mul_one]

theorem c_sq : (z 3 * z 2 * w) * (z 3 * z 2 * w) = 1 := by
  have hBC : Commute (z 3) (z 2) := hR.comm_zz 3 2
  have hBw : Commute (z 3) w := hR.comm_zw 3
  have hCw : Commute (z 2) w := hR.comm_zw 2
  have hBCw : Commute (z 3 * z 2) w := hBw.mul_left hCw
  rw [← pow_two, hBCw.mul_pow, hBC.mul_pow, pow_two, pow_two, pow_two, hR.sq_z 3, hR.sq_z 2,
    hR.sq_w]
  simp

end FiveRel

theorem fcomm_u_eq {a : Fin 5 → G} {z₀ : G} (hz : z₀ * z₀ = 1) (hsq : ∀ i, a i * a i = 1)
    (h3 : z₀ * a 2 * z₀ = a 3) (h4 : z₀ * a 1 * z₀ = a 4) :
    fcomm (a 2 * a 1) z₀ = a 1 * a 2 * a 3 * a 4 ∧
      fcomm (a 2 * a 1)⁻¹ z₀ = a 2 * a 1 * (a 4 * a 3) := by
  have hz' : z₀⁻¹ = z₀ := inv_eq_of_mul_eq_one_right hz
  have hinv : (a 2 * a 1)⁻¹ = a 1 * a 2 := inv_eq_of_mul_eq_one_right (by
    calc a 2 * a 1 * (a 1 * a 2) = a 2 * (a 1 * a 1) * a 2 := by simp only [mul_assoc]
      _ = 1 := by rw [hsq 1, mul_one, hsq 2])
  constructor
  · unfold fcomm
    rw [hinv, hz']
    have : z₀ * (a 2 * a 1) * z₀ = a 3 * a 4 := by rw [conj_mul hz, h3, h4]
    calc a 1 * a 2 * z₀ * (a 2 * a 1) * z₀ = a 1 * a 2 * (z₀ * (a 2 * a 1) * z₀) := by
          simp only [mul_assoc]
      _ = a 1 * a 2 * a 3 * a 4 := by rw [this]; simp only [mul_assoc]
  · unfold fcomm
    rw [inv_inv, hinv, hz']
    have : z₀ * (a 1 * a 2) * z₀ = a 4 * a 3 := by rw [conj_mul hz, h4, h3]
    calc a 2 * a 1 * z₀ * (a 1 * a 2) * z₀ = a 2 * a 1 * (z₀ * (a 1 * a 2) * z₀) := by
          simp only [mul_assoc]
      _ = a 2 * a 1 * (a 4 * a 3) := by rw [this]

end Sec8P2F

end CFSG.Quasithin.Fan86
