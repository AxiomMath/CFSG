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

namespace FiveTransitive.Degree43LongSylowData

open MulAction Subgroup

private theorem factorization_eq_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 43)
    (h5 : IsMultiplyPretransitive P X 5)
    {p : ℕ} (hp : p = 41 ∨ p = 43)
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
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hn := hfree s hs
  rw [← hm,Nat.factorization_mul (by norm_num) Nat.card_pos.ne',Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hn,add_zero]
  rcases hp with rfl | rfl
  · rw [show 115511760 = 41 * 2817360 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),Finsupp.add_apply,
      (show Nat.Prime 41 by norm_num).factorization,Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),add_zero]
  · rw [show 115511760 = 43 * 2686320 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),Finsupp.add_apply,
      (show Nat.Prime 43 by norm_num).factorization,Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),add_zero]

theorem sylow_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 43)
    (h5 : IsMultiplyPretransitive P X 5)
    {p : ℕ} (hp : p = 41 ∨ p = 43)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s)) (S : Sylow p P) : Nat.card S = p := by
  let _ : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> norm_num⟩
  rw [S.card_eq_multiplicity,factorization_eq_one P hcard h5 hp hfree,pow_one]

end FiveTransitive.Degree43LongSylowData

end CFSG
