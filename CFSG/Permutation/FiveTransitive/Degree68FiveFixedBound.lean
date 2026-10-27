module

public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport

public section

namespace CFSG

namespace FiveTransitive.Degree68FiveFixedBound
open MulAction

theorem nonidentity_fixed_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 68)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q)
    (q : Q) (hq : q ≠ 1) : Nat.card (fixedBy X q) ≤ 33 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hne : q.val.val ≠ 1 := fun he => hq (Subtype.ext (Subtype.ext he))
  have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt
    q.val.property hne
  rw [hcard] at hb
  have hbound : Nat.card (Function.fixedPoints q.val.val) ≤ 34 := by
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,q.val.val.sum_cycleType,hcard]
    omega
  obtain ⟨e,he⟩ := IsPGroup.iff_orderOf.mp hQ q
  let f : Function.End X := q.val.val.toFun
  have hf : f ^ (5 ^ e) = 1 := by
    funext x
    change ((q ^ (5 ^ e)).val.val) x = x
    rw [← he,pow_orderOf_eq_one]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 5) (n := e) hf
  change Fintype.card X % 5 = Fintype.card (Function.fixedPoints q.val.val) % 5 at hm
  rw [hcard,← Nat.card_eq_fintype_card] at hm
  change Nat.card (Function.fixedPoints q.val.val) ≤ 33
  omega

end FiveTransitive.Degree68FiveFixedBound

end CFSG
