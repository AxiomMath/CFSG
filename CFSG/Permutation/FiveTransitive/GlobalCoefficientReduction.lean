module

public import CFSG.Permutation.FiveTransitive.Reduction

public section

namespace CFSG

namespace FiveTransitive.GlobalCoefficientReduction

open MulAction Subgroup

theorem index_fixingSubgroup_five_eq_descFactorial
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (s : Set X) (hs : s.ncard = 5) :
    (fixingSubgroup P s).index =
      (Fintype.card X).descFactorial 5 := by
  have h5s :
      MulAction.IsMultiplyPretransitive P X s.ncard := by
    simpa only [hs] using h5
  have hindex := h5s.index_of_fixingSubgroup_eq s
  rw [hs] at hindex
  calc
    (fixingSubgroup P s).index =
        (Fintype.card X).choose 5 * (5 : ℕ).factorial := by
      simpa only [Nat.card_eq_fintype_card] using hindex
    _ = (Fintype.card X).descFactorial 5 := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.mul_comm _ _

end FiveTransitive.GlobalCoefficientReduction

end CFSG
