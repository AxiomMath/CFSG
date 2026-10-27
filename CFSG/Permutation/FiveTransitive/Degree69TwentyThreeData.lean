module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt

public section

namespace CFSG

namespace FiveTransitive.Degree69TwentyThreeData

open MulAction Subgroup

theorem factorization_eq_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5)
    {p : ℕ} (hp : p = 23)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s)) : (Nat.card P).factorization p = 1 := by
  classical
  let _ := h5
  obtain ⟨s,_,hs⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set X).ncard by simp [Set.ncard_univ,hcard])
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq (G := P) s (by rwa [hs])
  rw [Nat.card_eq_fintype_card,hcard,hs] at hi
  norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial] at hi
  have hm := (fixingSubgroup P s).index_mul_card
  rw [hi] at hm
  have hprime : p.Prime := by subst p; norm_num
  have hn := hfree s hs
  rw [← hm,Nat.factorization_mul (by norm_num) Nat.card_pos.ne',Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hn,add_zero]
  subst p
  rw [show 1348621560 = 23 * 58635720 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num),Finsupp.add_apply,
    (show Nat.Prime 23 by norm_num).factorization,Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num),add_zero]

theorem sylow_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5)
    {p : ℕ} (hp : p = 23)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s)) (S : Sylow p P) : Nat.card S = p := by
  let _ : Fact p.Prime := ⟨by subst p; norm_num⟩
  rw [S.card_eq_multiplicity,factorization_eq_one P hcard h5 hp hfree,pow_one]

private theorem element_fixed_lt_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (_hcard : Fintype.card X = 69)
    (_h5 : IsMultiplyPretransitive P X 5)
    {p : ℕ} (_hp : p = 23)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s)) (u : P) (hu : orderOf u = p) :
    Nat.card (Function.fixedPoints u.val) < 5 := by
  classical
  by_contra hn
  have hlarge : 5 ≤ (Function.fixedPoints u.val).ncard := by
    rw [← Nat.card_coe_set_eq]; omega
  obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hlarge
  let v : fixingSubgroup P s := ⟨u,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
  have hv : orderOf v = p := by rw [← Subgroup.orderOf_coe v]; exact hu
  have hd : p ∣ Nat.card (fixingSubgroup P s) := hv ▸ orderOf_dvd_natCard v
  exact hfree s hs hd

theorem element_cycle_type
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5)
    {p : ℕ} (hp : p = 23)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s)) (u : P) (hu : orderOf u = p) :
    u.val.cycleType = Multiset.replicate (69 / p) p := by
  have hg : orderOf u.val = p := (Subgroup.orderOf_coe u).trans hu
  obtain ⟨k,hk⟩ := Equiv.Perm.cycleType_prime_order (σ := u.val)
    (by rw [hg]; subst p; norm_num)
  have hsum := u.val.sum_cycleType
  rw [hk,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hg] at hsum
  have hle : u.val.support.card ≤ 69 := hcard ▸ Finset.card_le_univ u.val.support
  have hfix := element_fixed_lt_five P hcard h5 hp hfree u hu
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,u.val.sum_cycleType,hcard] at hfix
  have he : k + 1 = 69 / p := by subst p; omega
  rw [hk,hg,he]

end FiveTransitive.Degree69TwentyThreeData

end CFSG
