module

public import CFSG.Permutation.FiveTransitive.Degree72ElevenCentralizingBound
public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport

public section

namespace CFSG

namespace FiveTransitive.Degree72ElevenCentralizingActual
open MulAction

theorem card_eq_eleven
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) [IsMulCommutative Q]
    (hcommon : Nat.card (fixedPoints Q X) = 6)
    (horbit : ∀ x : X, x ∉ fixedPoints Q X → Nat.card (orbit Q x) = 11)
    (g : Subgroup.normalizer (Q : Set P)) (hg : orderOf g = 5)
    (hcomm : ∀ q : Q, g.val * q.val = q.val * g.val) : Nat.card Q = 11 := by
  apply Degree72ElevenCentralizingBound.card_eq_eleven hcard Q hcommon horbit _ g hg hcomm
  intro a ha
  have hne : a.val ≠ 1 := fun he => ha (Subtype.ext he)
  have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5
    hnotAlt a.property hne
  rw [hcard] at hb
  change Nat.card (Function.fixedPoints a.val) ≤ 36
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,a.val.sum_cycleType,hcard]
  omega

end FiveTransitive.Degree72ElevenCentralizingActual

end CFSG
