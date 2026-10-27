module

public import CFSG.Permutation.FiveTransitive.Degree67TwoEntrance
public import CFSG.Permutation.FiveTransitive.Degree67TwoSevenGeometry
public import CFSG.Permutation.FiveTransitive.Degree67TwoSevenBound
public import CFSG.Permutation.FiveTransitive.Degree67TwoFixedBound
public import CFSG.Permutation.FiveTransitive.Degree67FiveFree

public section

namespace CFSG

namespace FiveTransitive.Degree67TwoSevenOrder
open MulAction SylowFixedActionCore

theorem card_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hF : Nat.card (sylowFixedPoints X P s S) = 7) : Nat.card S ≤ 65536 := by
  classical
  let Q := sylowImage X P s S
  have hQ : IsPGroup 2 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQcard : Nat.card Q = Nat.card S :=
    Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  have hAlt := Degree67TwoEntrance.alternating_image P hcard h5 s hs S
  have hQfixed : Nat.card (fixedPoints Q X) = 7 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF
  have horbit := Degree67TwoSevenGeometry.orbits_le_four P hcard Q hQ hF hAlt
    (Degree67FiveFree.fixed_card_eq_two P hcard h5 hnotAlt)
    (Degree67SevenFree.fixed_card_eq_four P hcard h5 hnotAlt)
  rw [← hQcard]
  exact Degree67TwoSevenBound.card_le hcard Q hQ hQfixed horbit
    (Degree67TwoFixedBound.nonidentity_fixed_le P hcard h5 hnotAlt Q)

end FiveTransitive.Degree67TwoSevenOrder

end CFSG
