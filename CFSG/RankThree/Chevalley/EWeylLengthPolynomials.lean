module

public import CFSG.Timmesfeld.Orders.ExceptionalWeylData

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders
open Polynomial

theorem geom_mul_geom_pow {R : Type*} [CommSemiring R] (x : R) (m n : ℕ) :
    (∑ i ∈ Finset.range m, x ^ i) * ∑ j ∈ Finset.range n, x ^ (m * j) =
      ∑ k ∈ Finset.range (m * n), x ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, mul_add_one, Finset.sum_range_add, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_add, add_comm]

theorem geom_eq_mul_geom_pow {R : Type*} [CommSemiring R] (x : R) {m n d : ℕ}
    (h : m * n = d) :
    ∑ k ∈ Finset.range d, x ^ k =
      (∑ i ∈ Finset.range m, x ^ i) * ∑ j ∈ Finset.range n, x ^ (m * j) := by
  rw [geom_mul_geom_pow, h]

theorem eq_of_forall_natCast_eval_eq {P Q : ℤ[X]} (h : ∀ n : ℕ, P.eval (n : ℤ) = Q.eval (n : ℤ)) :
    P = Q :=
  Polynomial.eq_of_infinite_eval_eq P Q
    ((Set.infinite_range_of_injective Nat.cast_injective).mono (by
      rintro _ ⟨n, rfl⟩
      exact h n))

theorem sum_length_E6_eq [Fintype (WeylGroup .E6)] (q : ℕ) :
    ∑ w : WeylGroup .E6, q ^ (coxeterSystem .E6).length w =
      (([2, 5, 6, 8, 9, 12] : List ℕ).map fun d => ∑ i ∈ Finset.range d, q ^ i).prod := by
  rw [sum_length_E6]
  simp only [geomSum, one_mul, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rw [geom_eq_mul_geom_pow q (show 3 * 2 = 6 from rfl),
    geom_eq_mul_geom_pow q (show 4 * 3 = 12 from rfl)]
  ring

theorem sum_length_E7_eq [Fintype (WeylGroup .E7)] (q : ℕ) :
    ∑ w : WeylGroup .E7, q ^ (coxeterSystem .E7).length w =
      (([2, 6, 8, 10, 12, 14, 18] : List ℕ).map fun d => ∑ i ∈ Finset.range d, q ^ i).prod := by
  rw [sum_length_E7]
  simp only [geomSum, one_mul, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rw [geom_eq_mul_geom_pow q (show 3 * 2 = 6 from rfl),
    geom_eq_mul_geom_pow q (show 5 * 2 = 10 from rfl),
    geom_eq_mul_geom_pow q (show 4 * 3 = 12 from rfl),
    geom_eq_mul_geom_pow q (show 9 * 2 = 18 from rfl)]
  ring

theorem sum_length_E8_eq [Fintype (WeylGroup .E8)] (q : ℕ) :
    ∑ w : WeylGroup .E8, q ^ (coxeterSystem .E8).length w =
      (([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ).map
        fun d => ∑ i ∈ Finset.range d, q ^ i).prod := by
  rw [sum_length_E8]
  simp only [geomSum, one_mul, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rw [geom_eq_mul_geom_pow q (show 10 * 2 = 20 from rfl),
    geom_eq_mul_geom_pow q (show 6 * 5 = 30 from rfl),
    geom_eq_mul_geom_pow q (show 5 * 2 = 10 from rfl),
    geom_eq_mul_geom_pow q (show 3 * 2 = 6 from rfl),
    geom_eq_mul_geom_pow q (show 4 * 3 = 12 from rfl),
    geom_eq_mul_geom_pow q (show 9 * 2 = 18 from rfl)]
  ring

theorem E6_weyl_length_polynomial [Fintype (WeylGroup .E6)] :
    ∑ w : WeylGroup .E6, (X : ℤ[X]) ^ (coxeterSystem .E6).length w =
        (([2, 5, 6, 8, 9, 12] : List ℕ).map fun d => ∑ i ∈ Finset.range d, (X : ℤ[X]) ^ i).prod ∧
      Nat.card (WeylGroup .E6) = 51840 := by
  refine ⟨eq_of_forall_natCast_eval_eq fun n => ?_, ?_⟩
  · have h := congrArg (Nat.cast : ℕ → ℤ) (sum_length_E6_eq n)
    simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_mul, Nat.cast_one, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil] at h
    simpa only [eval_finsetSum, eval_pow, eval_X, eval_mul, eval_one, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil] using h
  · have h := sum_length_E6_eq 1
    simp only [one_pow, Finset.sum_const, Finset.card_univ, Finset.card_range, smul_eq_mul,
      mul_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] at h
    rw [Nat.card_eq_fintype_card, h]

theorem E7_weyl_length_polynomial [Fintype (WeylGroup .E7)] :
    ∑ w : WeylGroup .E7, (X : ℤ[X]) ^ (coxeterSystem .E7).length w =
        (([2, 6, 8, 10, 12, 14, 18] : List ℕ).map
          fun d => ∑ i ∈ Finset.range d, (X : ℤ[X]) ^ i).prod ∧
      Nat.card (WeylGroup .E7) = 2903040 := by
  refine ⟨eq_of_forall_natCast_eval_eq fun n => ?_, ?_⟩
  · have h := congrArg (Nat.cast : ℕ → ℤ) (sum_length_E7_eq n)
    simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_mul, Nat.cast_one, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil] at h
    simpa only [eval_finsetSum, eval_pow, eval_X, eval_mul, eval_one, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil] using h
  · have h := sum_length_E7_eq 1
    simp only [one_pow, Finset.sum_const, Finset.card_univ, Finset.card_range, smul_eq_mul,
      mul_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] at h
    rw [Nat.card_eq_fintype_card, h]

theorem E8_weyl_length_polynomial [Fintype (WeylGroup .E8)] :
    ∑ w : WeylGroup .E8, (X : ℤ[X]) ^ (coxeterSystem .E8).length w =
        (([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ).map
          fun d => ∑ i ∈ Finset.range d, (X : ℤ[X]) ^ i).prod ∧
      Nat.card (WeylGroup .E8) = 696729600 := by
  refine ⟨eq_of_forall_natCast_eval_eq fun n => ?_, ?_⟩
  · have h := congrArg (Nat.cast : ℕ → ℤ) (sum_length_E8_eq n)
    simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_mul, Nat.cast_one, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil] at h
    simpa only [eval_finsetSum, eval_pow, eval_X, eval_mul, eval_one, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil] using h
  · have h := sum_length_E8_eq 1
    simp only [one_pow, Finset.sum_const, Finset.card_univ, Finset.card_range, smul_eq_mul,
      mul_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] at h
    rw [Nat.card_eq_fintype_card, h]

end CFSG.RankThree.Chevalley
