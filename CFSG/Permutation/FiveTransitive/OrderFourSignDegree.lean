module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG

namespace FiveTransitive.OrderFourSignDegree

open Equiv

private theorem cycle_type_four
    {X : Type*} [Fintype X] [DecidableEq X] (g : Perm X)
    (h4 : g ^ 4 = 1) (hfree : ∀ x, (g ^ 2 : Perm X) x ≠ x) :
    g.cycleType = Multiset.replicate g.cycleType.card 4 := by
  apply Multiset.eq_replicate_of_mem
  intro n hn
  have hn2 := Perm.two_le_of_mem_cycleType hn
  have hd := (Perm.dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one h4)
  have hn24 : n = 2 ∨ n = 4 := by
    have hle : n ≤ 4 := Nat.le_of_dvd (by decide) hd
    interval_cases n <;> norm_num at *
  rcases hn24 with rfl | h
  · obtain ⟨c, t, hct, hdis, hc, hcard⟩ := Perm.mem_cycleType_iff.mp hn
    have hc2 : c ^ 2 = 1 := by rw [← hcard, ← hc.orderOf]; exact pow_orderOf_eq_one c
    obtain ⟨x, hx⟩ : ∃ x, c x ≠ x := by
      by_contra! h
      exact hc.ne_one (Perm.ext h)
    have htx : t x = x := (hdis x).resolve_left hx
    apply False.elim
    apply hfree x
    rw [hct, hdis.commute.mul_pow, hc2, one_mul, pow_two, Perm.mul_apply, htx, htx]
  · exact h

private theorem four_cycle_card_and_sign
    {X : Type*} [Fintype X] [DecidableEq X] (g : Perm X)
    (h4 : g ^ 4 = 1) (hfree : ∀ x, (g ^ 2 : Perm X) x ≠ x) :
    ∃ k : ℕ, Fintype.card X = 4 * k ∧ g.sign = (-1) ^ k := by
  have hc := cycle_type_four g h4 hfree
  have hs : g.support = Finset.univ := by
    ext x
    simp only [Perm.mem_support, Finset.mem_univ, iff_true]
    intro hx
    apply hfree x
    simp only [pow_two, Perm.mul_apply, hx]
  have hsum := g.sum_cycleType
  rw [hc, Multiset.sum_replicate, nsmul_eq_mul, hs, Finset.card_univ] at hsum
  have hsum' : g.cycleType.card * 4 = Fintype.card X := by simpa only [Nat.cast_id] using hsum
  refine ⟨g.cycleType.card, by omega, ?_⟩
  rw [Perm.sign_of_cycleType, hc, Multiset.sum_replicate, Multiset.card_replicate, nsmul_eq_mul]
  have he (k : ℕ) : ((-1 : ℤˣ) ^ (k * 4 + k)) = (-1) ^ k := by
    rw [pow_add, Nat.mul_comm k 4, pow_mul, show (-1 : ℤˣ) ^ 4 = 1 by decide, one_pow, one_mul]
  exact he _

theorem degree_mod_eight
    {X : Type*} [Fintype X] [DecidableEq X] (g : Perm X)
    (h4 : g ^ 4 = 1) (hsign : g.sign = 1)
    (hfree : ∀ x, g x ≠ x)
    (htwo : Fintype.card (Function.fixedPoints (g ^ 2 : Perm X)) = 2) :
    Fintype.card X % 8 = 6 := by
  let p : X → Prop := fun x => (g ^ 2 : Perm X) x = x
  have hstable (x : X) : p (g x) ↔ p x := by
    change g (g (g x)) = g x ↔ g (g x) = x
    exact g.injective.eq_iff
  let u : Perm {x // p x} := g.subtypePerm hstable
  let v : Perm {x // ¬ p x} := g.subtypePerm (fun x => not_congr (hstable x))
  have hu2 : u ^ 2 = 1 := by
    ext x
    exact x.property
  have huFree (x : {x // p x}) : u x ≠ x := by
    intro h
    exact hfree x.val (congrArg Subtype.val h)
  have huSupport : u.support = Finset.univ := by
    ext x
    simp only [Perm.mem_support, Finset.mem_univ, iff_true]
    exact huFree x
  have huCard : Fintype.card {x // p x} = 2 := htwo
  have huType : u.cycleType = {2} := by
    have hct := Perm.cycleType_of_pow_prime_eq_one hu2
    have hs := u.sum_cycleType
    rw [hct, Multiset.sum_replicate, nsmul_eq_mul, huSupport, Finset.card_univ, huCard] at hs
    have hs' : u.cycleType.card * 2 = 2 := by simpa only [Nat.cast_id] using hs
    have hc : u.cycleType.card = 1 := by omega
    rw [hct, hc]
    rfl
  have huSign : u.sign = -1 := by rw [Perm.sign_of_cycleType, huType]; decide
  have hv4 : v ^ 4 = 1 := by
    ext x
    change ((g ^ 4 : Perm X) x.val) = x.val
    rw [h4, Perm.one_apply]
  have hvFree (x : {x // ¬ p x}) : (v ^ 2 : Perm {x // ¬ p x}) x ≠ x := by
    intro h
    exact x.property (congrArg Subtype.val h)
  obtain ⟨k, hk, hksign⟩ := four_cycle_card_and_sign v hv4 hvFree
  have hdecomp : u.subtypeCongr v = g := by
    ext x
    rw [Perm.subtypeCongr.apply]
    split <;> rfl
  have hsign' : (-1 : ℤˣ) * (-1) ^ k = 1 := by
    calc
      (-1 : ℤˣ) * (-1) ^ k = u.sign * v.sign := by rw [huSign, hksign]
      _ = g.sign := by rw [← Perm.sign_subtypeCongr, hdecomp]
      _ = 1 := hsign
  have hkodd : k % 2 = 1 := by
    by_contra h
    have hkzero : k % 2 = 0 := by omega
    have heven : Even k := Nat.even_iff.mpr hkzero
    rw [heven.neg_one_pow, mul_one] at hsign'
    norm_num at hsign'
  have hcard : Fintype.card {x // p x} + Fintype.card {x // ¬ p x} = Fintype.card X :=
    by
      have h := Fintype.card_subtype_compl p
      have hle := Fintype.card_subtype_le p
      omega
  rw [huCard, hk] at hcard
  omega

end FiveTransitive.OrderFourSignDegree

end CFSG
