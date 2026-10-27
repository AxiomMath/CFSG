module

public import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.SetLike

public section

namespace CFSG.StandardType.SporadicShape

private theorem gkc_pow_x_mul_y {G : Type*} [Group G] {x y z : G} (hzx : z * x = x * z)
    (h : x * y = y * x * z ^ 9) (n : ℕ) : x ^ n * y = y * x ^ n * z ^ (9 * n) := by
  have hc : ∀ k : ℕ, z ^ k * x = x * z ^ k := fun k => ((Commute.pow_left hzx k)).eq
  induction n with
  | zero => simp
  | succ n ih =>
    calc x ^ (n + 1) * y = x * (x ^ n * y) := by rw [pow_succ', mul_assoc]
      _ = x * (y * x ^ n * z ^ (9 * n)) := by rw [ih]
      _ = (x * y) * x ^ n * z ^ (9 * n) := by simp only [mul_assoc]
      _ = y * x * z ^ 9 * x ^ n * z ^ (9 * n) := by rw [h]
      _ = y * x * (z ^ 9 * x ^ n) * z ^ (9 * n) := by simp only [mul_assoc]
      _ = y * x * (x ^ n * z ^ 9) * z ^ (9 * n) := by
        rw [((Commute.pow_left (Commute.pow_right hzx n) 9)).eq]
      _ = y * (x * x ^ n) * (z ^ 9 * z ^ (9 * n)) := by simp only [mul_assoc]
      _ = y * x ^ (n + 1) * z ^ (9 * (n + 1)) := by
        rw [← pow_succ', ← pow_add]; congr 2; ring



private theorem gkc_pow_x_mul_pow_y {G : Type*} [Group G] {x y z : G} (hzx : z * x = x * z)
    (hzy : z * y = y * z)
    (h : x * y = y * x * z ^ 9) (n m : ℕ) :
    x ^ n * y ^ m = y ^ m * x ^ n * z ^ (9 * n * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc x ^ n * y ^ (m + 1) = (x ^ n * y ^ m) * y := by rw [pow_succ, mul_assoc]
      _ = y ^ m * x ^ n * z ^ (9 * n * m) * y := by rw [ih]
      _ = y ^ m * x ^ n * (z ^ (9 * n * m) * y) := by simp only [mul_assoc]
      _ = y ^ m * x ^ n * (y * z ^ (9 * n * m)) := by
        rw [((Commute.pow_left hzy (9 * n * m))).eq]
      _ = y ^ m * (x ^ n * y) * z ^ (9 * n * m) := by simp only [mul_assoc]
      _ = y ^ m * (y * x ^ n * z ^ (9 * n)) * z ^ (9 * n * m) := by
        rw [gkc_pow_x_mul_y hzx h n]
      _ = y ^ (m + 1) * x ^ n * (z ^ (9 * n) * z ^ (9 * n * m)) := by
        rw [pow_succ]; simp only [mul_assoc]
      _ = y ^ (m + 1) * x ^ n * z ^ (9 * n * (m + 1)) := by
        rw [← pow_add]; congr 2; ring



private theorem gkc_nf_mul {G : Type*} [Group G] {x y z : G} (hzx : z * x = x * z)
    (hzy : z * y = y * z)
    (hxy : x * y = y * x * z ^ 9) (a b c d e f : ℕ) :
    (z ^ d * (y ^ e * x ^ f)) * (z ^ a * (y ^ b * x ^ c)) =
      z ^ (d + a + 9 * f * b) * (y ^ (e + b) * x ^ (f + c)) := by
  have hcx : ∀ k n : ℕ, z ^ k * x ^ n = x ^ n * z ^ k := fun k n => (Commute.pow_pow hzx k n).eq
  have hcy : ∀ k n : ℕ, z ^ k * y ^ n = y ^ n * z ^ k := fun k n => (Commute.pow_pow hzy k n).eq
  have hmx : ∀ (k n : ℕ) (w : G), x ^ n * (z ^ k * w) = z ^ k * (x ^ n * w) := by
    intro k n w; rw [← mul_assoc, ← hcx k n, mul_assoc]
  have hmy : ∀ (k n : ℕ) (w : G), y ^ n * (z ^ k * w) = z ^ k * (y ^ n * w) := by
    intro k n w; rw [← mul_assoc, ← hcy k n, mul_assoc]
  have h1 := gkc_pow_x_mul_pow_y hzx hzy hxy f b
  calc (z ^ d * (y ^ e * x ^ f)) * (z ^ a * (y ^ b * x ^ c))
      = z ^ d * (y ^ e * (x ^ f * (z ^ a * (y ^ b * x ^ c)))) := by simp only [mul_assoc]
    _ = z ^ d * (y ^ e * (z ^ a * (x ^ f * (y ^ b * x ^ c)))) := by rw [hmx a f]
    _ = z ^ d * (z ^ a * (y ^ e * (x ^ f * (y ^ b * x ^ c)))) := by rw [hmy a e]
    _ = z ^ d * (z ^ a * (y ^ e * ((x ^ f * y ^ b) * x ^ c))) := by simp only [mul_assoc]
    _ = z ^ d * (z ^ a * (y ^ e * ((y ^ b * x ^ f * z ^ (9 * f * b)) * x ^ c))) := by rw [h1]
    _ = z ^ d * (z ^ a * (y ^ e * (y ^ b * (x ^ f * (z ^ (9 * f * b) * x ^ c))))) := by
        simp only [mul_assoc]
    _ = z ^ d * (z ^ a * (y ^ e * (y ^ b * (z ^ (9 * f * b) * (x ^ f * x ^ c))))) := by
        rw [hmx (9 * f * b) f]
    _ = z ^ d * (z ^ a * (y ^ e * (z ^ (9 * f * b) * (y ^ b * (x ^ f * x ^ c))))) := by
        rw [hmy (9 * f * b) b]
    _ = z ^ d * (z ^ a * (z ^ (9 * f * b) * (y ^ e * (y ^ b * (x ^ f * x ^ c))))) := by
        rw [hmy (9 * f * b) e]
    _ = z ^ (d + a + 9 * f * b) * (y ^ (e + b) * x ^ (f + c)) := by
        rw [pow_add, pow_add, pow_add, pow_add]
        simp only [mul_assoc]




theorem heis13_conj_z {G : Type*} [Group G] {x y z h : G} (hz : z ^ 13 = 1)
    (hzx : z * x = x * z) (hzy : z * y = y * z) (hyx : y * x = x * (y * z ^ 4))
    {a b c d e f : ℕ} (hhx : h * x = z ^ a * (y ^ b * (x ^ c * h)))
    (hhy : h * y = z ^ d * (y ^ e * (x ^ f * h))) :
    h * z * h⁻¹ = z ^ ((c : ℤ) * e - f * b) := by
  have hz4 : z ^ 4 * z ^ 9 = 1 := by rw [← pow_add]; exact hz
  have hxy : x * y = y * x * z ^ 9 := by
    calc x * y = x * y * (z ^ 4 * z ^ 9) := by rw [hz4, mul_one]
      _ = (x * (y * z ^ 4)) * z ^ 9 := by simp only [mul_assoc]
      _ = y * x * z ^ 9 := by rw [← hyx]
  have hX : h * x * h⁻¹ = z ^ a * (y ^ b * x ^ c) := by
    calc h * x * h⁻¹ = (z ^ a * (y ^ b * (x ^ c * h))) * h⁻¹ := by rw [hhx]
      _ = z ^ a * (y ^ b * x ^ c) := by simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hY : h * y * h⁻¹ = z ^ d * (y ^ e * x ^ f) := by
    calc h * y * h⁻¹ = (z ^ d * (y ^ e * (x ^ f * h))) * h⁻¹ := by rw [hhy]
      _ = z ^ d * (y ^ e * x ^ f) := by simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hconj : (h * y * h⁻¹) * (h * x * h⁻¹) =
      (h * x * h⁻¹) * ((h * y * h⁻¹) * (h * z * h⁻¹) ^ 4) := by
    calc (h * y * h⁻¹) * (h * x * h⁻¹) = h * (y * x) * h⁻¹ := by group
      _ = h * (x * (y * z ^ 4)) * h⁻¹ := by rw [hyx]
      _ = (h * x * h⁻¹) * ((h * y * h⁻¹) * (h * z * h⁻¹) ^ 4) := by rw [conj_pow]; group
  set W0 : G := y ^ (e + b) * x ^ (f + c) with hW0
  set Z' : G := h * z * h⁻¹ with hZ'
  have hYX : (h * y * h⁻¹) * (h * x * h⁻¹) = z ^ (d + a + 9 * f * b) * W0 := by
    rw [hX, hY, gkc_nf_mul hzx hzy hxy a b c d e f]
  have hXY : (h * x * h⁻¹) * (h * y * h⁻¹) = z ^ (a + d + 9 * c * e) * W0 := by
    rw [hX, hY, gkc_nf_mul hzx hzy hxy d e f a b c, add_comm b e, add_comm c f]
  have hZ4 : Z' ^ 4 = ((h * x * h⁻¹) * (h * y * h⁻¹))⁻¹ * ((h * y * h⁻¹) * (h * x * h⁻¹)) := by
    calc Z' ^ 4 = ((h * x * h⁻¹) * (h * y * h⁻¹))⁻¹ *
          ((h * x * h⁻¹) * ((h * y * h⁻¹) * Z' ^ 4)) := by group
      _ = _ := by rw [← hconj]
  have hcW : Commute z W0 :=
    (Commute.pow_right (show Commute z y from hzy) (e + b)).mul_right
      (Commute.pow_right (show Commute z x from hzx) (f + c))
  have hzk : ∀ k : ℤ, z ^ k * W0 = W0 * z ^ k := fun k => (Commute.zpow_left hcW k).eq
  have hpow : ∀ A B : ℕ, (z ^ A)⁻¹ * z ^ B = z ^ ((B : ℤ) - A) := by
    intro A B
    simp only [← zpow_natCast, ← zpow_neg, ← zpow_add]
    congr 1; ring
  have hZ4' : Z' ^ 4 = z ^ (((9 * f * b : ℕ) : ℤ) - ((9 * c * e : ℕ) : ℤ)) := by
    rw [hZ4, hXY, hYX]
    calc (z ^ (a + d + 9 * c * e) * W0)⁻¹ * (z ^ (d + a + 9 * f * b) * W0)
        = W0⁻¹ * ((z ^ (a + d + 9 * c * e))⁻¹ * z ^ (d + a + 9 * f * b)) * W0 := by
          simp only [mul_inv_rev, mul_assoc]
      _ = W0⁻¹ * z ^ (((d + a + 9 * f * b : ℕ) : ℤ) - ((a + d + 9 * c * e : ℕ) : ℤ)) * W0 := by
          rw [hpow]
      _ = z ^ (((d + a + 9 * f * b : ℕ) : ℤ) - ((a + d + 9 * c * e : ℕ) : ℤ)) := by
          rw [mul_assoc, hzk, inv_mul_cancel_left]
      _ = z ^ (((9 * f * b : ℕ) : ℤ) - ((9 * c * e : ℕ) : ℤ)) := by
          congr 1; push_cast; ring
  have hZ13 : Z' ^ 13 = 1 := by rw [hZ', conj_pow, hz]; group
  have hZ40 : Z' = (Z' ^ 4) ^ 10 := by
    rw [← pow_mul, show 4 * 10 = 13 * 3 + 1 by norm_num, pow_add, pow_mul, hZ13, one_pow,
      one_mul, pow_one]
  have hz13 : z ^ (13 : ℤ) = 1 := by
    have := zpow_natCast z 13
    simpa using this.trans hz
  have hk13 : ∀ k : ℤ, z ^ (13 * k) = 1 := fun k => by rw [zpow_mul, hz13, one_zpow]
  calc Z' = (Z' ^ 4) ^ 10 := hZ40
    _ = z ^ (10 * (((9 * f * b : ℕ) : ℤ) - ((9 * c * e : ℕ) : ℤ))) := by
        rw [hZ4', ← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
    _ = z ^ (((c : ℤ) * e - f * b) + 13 * (-7 * ((c : ℤ) * e - f * b))) := by
        congr 1; push_cast; ring
    _ = z ^ ((c : ℤ) * e - f * b) := by rw [zpow_add, hk13, mul_one]

end CFSG.StandardType.SporadicShape
