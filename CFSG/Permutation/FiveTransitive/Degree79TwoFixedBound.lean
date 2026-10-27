module

public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport

public section

namespace CFSG

namespace FiveTransitive.Degree79TwoFixedBound
open MulAction

theorem nonidentity_fixed_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (q : Q) (hq : q ≠ 1) : Nat.card (fixedBy X q) ≤ 39 := by
  have hne : q.val.val ≠ 1 := fun he => hq (Subtype.ext (Subtype.ext he))
  have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5
    hnotAlt q.val.property hne
  rw [hcard] at hb
  change Nat.card (Function.fixedPoints q.val.val) ≤ 39
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,q.val.val.sum_cycleType,hcard]
  omega

end FiveTransitive.Degree79TwoFixedBound

end CFSG
