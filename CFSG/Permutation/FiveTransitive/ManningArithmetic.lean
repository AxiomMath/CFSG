module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG

namespace FiveTransitive.ManningArithmetic

private theorem large_cycle_polynomial_positive (k x : ℤ) (hk : 1 ≤ k) (hx : 2*k+2 ≤ x) :
    0 < k*x^2 - (3*k^2+k-4)*x + 2*k^3-8*k-6 := by
  let d := x-(2*k+2)
  have hd : 0 ≤ d := by dsimp [d]; omega
  have hs : 0 ≤ k*d^2 := mul_nonneg (by omega) (sq_nonneg d)
  have hl : 0 ≤ (k^2+3*k+4)*d := mul_nonneg (by nlinarith [sq_nonneg k]) hd
  have he : k*x^2 - (3*k^2+k-4)*x + 2*k^3-8*k-6 =
      k*d^2+(k^2+3*k+4)*d+2*k+2 := by dsimp [d]; ring
  rw [he]
  omega

private theorem three_cycle_polynomial_positive (k x : ℤ) (hk : 1 ≤ k) (hx : 2*k+3 ≤ x) :
    0 < k*x^2 - (3*k^2+2*k-4)*x + 2*k^3+k^2-7*k-2 := by
  let d := x-(2*k+3)
  have hd : 0 ≤ d := by dsimp [d]; omega
  have hs : 0 ≤ k*d^2 := mul_nonneg (by omega) (sq_nonneg d)
  have hl : 0 ≤ (k^2+4*k+4)*d := mul_nonneg (by nlinarith [sq_nonneg k]) hd
  have he : k*x^2 - (3*k^2+2*k-4)*x + 2*k^3+k^2-7*k-2 =
      k*d^2+(k^2+4*k+4)*d+4*k+10 := by dsimp [d]; ring
  rw [he]
  omega

theorem large_cycle_inequality_bound (m n : ℕ) (hm : 8 ≤ m) (hmn : m ≤ n)
    (h : m*((n-3)*(n-4)) + 2*(m-3)*(n-4) + (m-2)*(m-3)*(m-4) +
      2*(m-1)*(n-4) + (m-1)*(m-2)*(m-6) ≤
        3*((n-3)*(n-4)) + 3*(m-1)*(m-3)*(n-4)) : n < 2*m := by
  by_contra hnot
  have hn : 2*m ≤ n := by omega
  have hm6 : 6 ≤ m := by omega
  have hm4 : 4 ≤ m := by omega
  have hm3 : 3 ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  have hn4 : 4 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  zify [hm6, hm4, hm3, hm2, hm1, hn4, hn3] at h
  have hpoly := large_cycle_polynomial_positive ((m : ℤ)-3) ((n : ℤ)-4)
    (by omega) (by omega)
  nlinarith

theorem three_cycle_inequality_bound (m n : ℕ) (hm : 8 ≤ m) (hmn : m ≤ n)
    (h : m*((n-3)*(n-4)) + 2*(n-m) + 2*(m-3)*(n-4) + (m-2)*(m-3)*(m-4) +
      (m-1)*(n-4) + (m-1)*(m-2)*(m-5) ≤
        3*((n-3)*(n-4)) + 3*(m-1)*(m-3)*(n-4)) : n ≤ 2*m := by
  by_contra hnot
  have hn : 2*m+1 ≤ n := by omega
  have hm5 : 5 ≤ m := by omega
  have hm4 : 4 ≤ m := by omega
  have hm3 : 3 ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  have hn4 : 4 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  zify [hm5, hm4, hm3, hm2, hm1, hn4, hn3, hmn] at h
  have hpoly := three_cycle_polynomial_positive ((m : ℤ)-3) ((n : ℤ)-4)
    (by omega) (by omega)
  nlinarith

end FiveTransitive.ManningArithmetic

end CFSG
