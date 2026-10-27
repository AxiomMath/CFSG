module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.CharP.Two

public section

namespace CFSG.Quasithin.H13.F431.G2.Cls

theorem c2_two {K : Type*} [CommRing K] [CharP K 2] : (2 : K) = 0 := CharTwo.two_eq_zero

theorem c2_three {K : Type*} [CommRing K] [CharP K 2] : (3 : K) = 1 := by
  linear_combination (c2_two (K := K))

theorem c2_four {K : Type*} [CommRing K] [CharP K 2] : (4 : K) = 0 := by
  linear_combination 2 * (c2_two (K := K))

theorem c2_five {K : Type*} [CommRing K] [CharP K 2] : (5 : K) = 1 := by
  linear_combination 2 * (c2_two (K := K))

theorem c2_six {K : Type*} [CommRing K] [CharP K 2] : (6 : K) = 0 := by
  linear_combination 3 * (c2_two (K := K))

theorem c2_seven {K : Type*} [CommRing K] [CharP K 2] : (7 : K) = 1 := by
  linear_combination 3 * (c2_two (K := K))

theorem c2_eight {K : Type*} [CommRing K] [CharP K 2] : (8 : K) = 0 := by
  linear_combination 4 * (c2_two (K := K))

macro "g2char2" : tactic => `(tactic| first
  | ring1
  | (try ring_nf
     try simp only [CharTwo.neg_eq, CharTwo.sub_eq_add, c2_two, c2_three, c2_four, c2_five,
       c2_six, c2_seven, c2_eight, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul,
       neg_zero, sub_zero, zero_sub]
     try ring_nf))

end CFSG.Quasithin.H13.F431.G2.Cls
