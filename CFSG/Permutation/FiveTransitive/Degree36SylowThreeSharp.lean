module

public import CFSG.Permutation.FiveTransitive.Degree36SylowThreeStructure
public import CFSG.Permutation.FiveTransitive.Degree36ThreeOrbitSharpBound

public section

namespace CFSG

namespace FiveTransitive.Degree36SylowThreeSharp

open MulAction SylowFixedActionCore

theorem card_le_eighty_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) : Nat.card S ≤ 81 := by
  by_cases hS : Nat.card S = 1
  · omega
  let Q := sylowImage X P s S
  have hF := (Degree36SmallPrimeEntrance.three_entrance P hcard h5 hnotAlt s hs S hS).1
  have hfixeq : (sylowFixedPoints X P s S : Set X) = fixedPoints Q X :=
    FixedNormalizerAction.fixed_eq Q
  have hfixed : Nat.card (fixedPoints Q X) = 6 := by rw [← hfixeq]; exact hF
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  rw [← hQcard]
  exact Degree36ThreeOrbitSharpBound.card_le_eighty_one P hcard h5 hnotAlt Q
    (S.isPGroup'.map (fixingSubgroup P s).subtype) hfixed
    (Degree36SylowThreeStructure.orbit_card_three P hcard h5 hnotAlt s hs S hS)

end FiveTransitive.Degree36SylowThreeSharp

end CFSG
