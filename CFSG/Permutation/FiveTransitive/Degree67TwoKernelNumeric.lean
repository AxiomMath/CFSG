module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.Degree67TwoKernelNumeric
open scoped BigOperators

theorem excluded
    {A : Type*} [DecidableEq A] (T : Finset A) (f : A → ℕ)
    (hcard : T.card = 31) (hbound : ∀ a ∈ T, f a ≤ 33)
    (hsum : ∑ a ∈ T, f a = 1021)
    (hdiv : 32 ∣ 4489 + ∑ a ∈ T, (f a)^2) : False := by
  have hlo (a : A) (ha : a ∈ T) : 31 ≤ f a := by
    have hb := Finset.sum_le_sum (s := T.erase a)
      (fun b hb => hbound b (Finset.mem_of_mem_erase hb))
    have hc : (T.erase a).card = 30 := by rw [Finset.card_erase_of_mem ha,hcard]
    simp only [Finset.sum_const,nsmul_eq_mul,hc] at hb
    have he := Finset.sum_erase_add T f ha
    omega
  have cases (a : A) (ha : a ∈ T) : f a = 31 ∨ f a = 32 ∨ f a = 33 := by
    have h1 := hlo a ha
    have h2 := hbound a ha
    omega
  have low := Finset.sum_le_sum (s := T) (fun a ha =>
    (show 66 * f a ≤ (f a)^2 + 1089 by rcases cases a ha with h | h | h <;> rw [h] <;> norm_num))
  have high := Finset.sum_le_sum (s := T) (fun a ha =>
    (show (f a)^2 + 1023 ≤ 64 * f a by
      rcases cases a ha with h | h | h <;> rw [h] <;> norm_num))
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,
    ← Finset.mul_sum,hcard,hsum] at low high
  obtain ⟨k,hk⟩ := hdiv
  omega

end FiveTransitive.Degree67TwoKernelNumeric

end CFSG
