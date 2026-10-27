module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Config
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.WeakClosure81

private theorem nine3_eq_one_of_pow_two_of_pow_three {Y : Type} [Group Y] {x : Y}
    (h2 : x ^ 2 = 1) (h3 : x ^ 3 = 1) : x = 1 := by
  calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; simp

private theorem nine3_mul_eq_one_of_comm_of_pow_three {Y : Type} [Group Y] {a b : Y}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (h3 : (a * b) ^ 3 = 1) :
    a * b = 1 := by
  apply nine3_eq_one_of_pow_two_of_pow_three _ h3
  calc (a * b) ^ 2 = a * b * (a * b) := pow_two _
    _ = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [← hab]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha, hb, one_mul]

theorem Nine3Config.not_comm_ae {Y : Type} [Group Y] {c a e a' v : Y}
    (h : Nine3Config c a e a' v) : a * e ≠ e * a := by
  intro hcomm
  have hae : a * e = 1 :=
    nine3_mul_eq_one_of_comm_of_pow_three h.sq_a h.sq_e hcomm h.pow_ae
  have hea : e = a := by
    have h1 : a⁻¹ = e := inv_eq_of_mul_eq_one_right hae
    have h2 : a⁻¹ = a := inv_eq_of_mul_eq_one_right h.sq_a
    rw [← h1, h2]
  apply h.ne_aa'
  apply nine3_mul_eq_one_of_comm_of_pow_three h.sq_a h.sq_a' h.comm_aa'
  rw [← hea]
  exact h.pow_ea'

theorem Nine3Config.orderOf_ae {Y : Type} [Group Y] {c a e a' v : Y}
    (h : Nine3Config c a e a' v) : orderOf (a * e) = 3 ∧ orderOf (e * a') = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨orderOf_eq_prime h.pow_ae ?_, orderOf_eq_prime h.pow_ea' ?_⟩
  · intro h1
    apply h.not_comm_ae
    rw [h1, (mul_eq_one_comm.mp h1)]
  · intro h1
    have hea : e = a' := by
      have h2 : e⁻¹ = a' := inv_eq_of_mul_eq_one_right h1
      have h3 : e⁻¹ = e := inv_eq_of_mul_eq_one_right h.sq_e
      rw [← h3, h2]
    apply h.ne_aa'
    apply nine3_mul_eq_one_of_comm_of_pow_three h.sq_a h.sq_a' h.comm_aa'
    rw [← hea]
    exact h.pow_ae

end CFSG.LocalAnalysis.WeakClosure81
