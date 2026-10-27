module

public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport

public section

namespace CFSG

namespace FiveTransitive.Degree60ThreeFixedBound

open MulAction

theorem eq_one_of_thirtyOne_fixed
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (q : Q) (hfixed : 31 ≤ (fixedBy X q).ncard) : q = 1 := by
  by_contra hq
  have hne : q.val.val ≠ 1 := fun he => hq (Subtype.ext (Subtype.ext he))
  have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5
    hnotAlt q.val.property hne
  rw [hcard] at hb
  change 31 ≤ (Function.fixedPoints q.val.val).ncard at hfixed
  rw [← Nat.card_coe_set_eq,Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,
    q.val.val.sum_cycleType,hcard] at hfixed
  omega

end FiveTransitive.Degree60ThreeFixedBound

end CFSG
