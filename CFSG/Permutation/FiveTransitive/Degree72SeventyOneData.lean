module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.NormNum.Prime
public import CFSG.Permutation.FiveTransitive.MinimalOrbitStabilizer

public section

namespace CFSG

namespace FiveTransitive.Degree72SeventyOneData
open MulAction Subgroup

private theorem factorization_eq_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ 71 ∣ Nat.card (fixingSubgroup P s)) : (Nat.card P).factorization 71 = 1 := by
  classical
  let _ := h5
  obtain ⟨s,_,hs⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set X).ncard by simp [Set.ncard_univ,hcard])
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq (G := P) s (by rwa [hs])
  rw [Nat.card_eq_fintype_card,hcard,hs] at hi
  norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial] at hi
  have hm := (fixingSubgroup P s).index_mul_card
  rw [hi] at hm
  have hn := hfree s hs
  rw [← hm,Nat.factorization_mul (by norm_num) Nat.card_pos.ne',Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hn,add_zero]
  rw [show 1678985280 = 71 * 23647680 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num),Finsupp.add_apply,
    (show Nat.Prime 71 by norm_num).factorization,Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num),add_zero]

theorem sylow_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ 71 ∣ Nat.card (fixingSubgroup P s))
    (S : Sylow 71 P) : Nat.card S = 71 := by
  let _ : Fact (Nat.Prime 71) := ⟨by norm_num⟩
  rw [S.card_eq_multiplicity,factorization_eq_one P hcard h5 hfree,pow_one]

end FiveTransitive.Degree72SeventyOneData

end CFSG
