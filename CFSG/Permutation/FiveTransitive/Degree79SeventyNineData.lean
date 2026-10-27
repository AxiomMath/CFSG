module

public import CFSG.Permutation.FiveTransitive.Degree79LargePrimeFree

public section

namespace CFSG

namespace FiveTransitive.Degree79SeventyNineData
open MulAction

private theorem factorization_eq_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    (Nat.card P).factorization 79 = 1 := by
  classical
  let _ := h5
  obtain ⟨s,_,hs⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set X).ncard by simp [Set.ncard_univ,hcard])
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq (G := P) s (by rwa [hs])
  rw [Nat.card_eq_fintype_card,hcard,hs] at hi
  norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial] at hi
  have hm := (fixingSubgroup P s).index_mul_card
  rw [hi] at hm
  have hn := Degree79LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs 79
    (by norm_num) (by norm_num)
  rw [← hm,Nat.factorization_mul (by norm_num) Nat.card_pos.ne',Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hn,add_zero]
  rw [show 2704501800 = 79 * 34234200 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num),Finsupp.add_apply,
    (show Nat.Prime 79 by norm_num).factorization,Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num),add_zero]

theorem sylow_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (S : Sylow 79 P) : Nat.card S = 79 := by
  let _ : Fact (Nat.Prime 79) := ⟨by norm_num⟩
  rw [S.card_eq_multiplicity,factorization_eq_one P hcard h5 hnotAlt,pow_one]

end FiveTransitive.Degree79SeventyNineData

end CFSG
