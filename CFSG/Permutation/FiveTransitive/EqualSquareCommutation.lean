module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs

public section

namespace CFSG

namespace FiveTransitive.EqualSquareCommutation

theorem commute_of_involution
    {G : Type*} [Group G] (x y : G) (hy : y ^ 2 = 1)
    (hxy : (x * y) ^ 2 = x ^ 2) : Commute x y := by
  have he : y * x * y = x := by
    apply mul_left_cancel (a := x)
    simpa only [pow_two, mul_assoc] using hxy
  have h := congrArg (fun t => t * y) he
  have hy' : y * y = 1 := by simpa only [pow_two] using hy
  simp only [mul_assoc, hy', mul_one] at h
  exact h.symm

theorem commute_of_equal_squares
    {G : Type*} [Group G] (a x z : G) (ha : a ^ 2 = 1)
    (hx : x ^ 2 = a) (hz : z ^ 2 = a) (hxz : (x * z) ^ 2 = 1) : Commute x z := by
  have hix : x⁻¹ = a * x := inv_eq_of_mul_eq_one_left (by
    rw [mul_assoc, ← pow_two, hx, ← pow_two, ha])
  have hiz : z⁻¹ = z * a := inv_eq_of_mul_eq_one_right (by
    rw [← mul_assoc, ← pow_two, hz, ← pow_two, ha])
  calc
    x * z = (x * z)⁻¹ := (inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hxz)).symm
    _ = z⁻¹ * x⁻¹ := mul_inv_rev _ _
    _ = (z * a) * (a * x) := by rw [hix, hiz]
    _ = z * x := by rw [mul_assoc z a (a * x), ← mul_assoc a a x, ← pow_two, ha, one_mul]

end FiveTransitive.EqualSquareCommutation

end CFSG
