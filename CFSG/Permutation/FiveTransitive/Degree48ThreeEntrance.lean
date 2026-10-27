module

public import CFSG.Permutation.FiveTransitive.Degree48ThreeSixExclusion
public import CFSG.Permutation.FiveTransitive.Degree48ThreeBound
public import CFSG.Permutation.FiveTransitive.Degree48SylowFiveOrder
public import CFSG.Permutation.FiveTransitive.Degree48ThreeFixedCases

public section

namespace CFSG

namespace FiveTransitive.Degree48ThreeEntrance

open MulAction SylowFixedActionCore

theorem three_entrance
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card (sylowFixedPoints X P s S) = 12 ∧ Nat.card S ≤ 6561 := by
  have hcases := Degree48ThreeFixedCases.three_fixed_card_cases P hcard h5 hnotAlt s hs S hS
  have hne := Degree48ThreeSixExclusion.fixed_ne_six P hcard h5
    (Degree48SylowFiveOrder.fixed_card_three_or_eight P hcard h5 hnotAlt) s hs S
  have hF : Nat.card (sylowFixedPoints X P s S) = 12 := hcases.resolve_left hne
  let Q := sylowImage X P s S
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  have hfixeq : (sylowFixedPoints X P s S : Set X) = fixedPoints Q X :=
    FixedNormalizerAction.fixed_eq Q
  have hbound := Degree48ThreeBound.three_card_le_6561 P hcard h5 hnotAlt Q
    (S.isPGroup'.map (fixingSubgroup P s).subtype) (by rw [← hfixeq,hF])
  exact ⟨hF,by rwa [hQcard] at hbound⟩

end FiveTransitive.Degree48ThreeEntrance

end CFSG
