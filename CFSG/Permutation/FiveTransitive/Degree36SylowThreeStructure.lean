module

public import CFSG.Permutation.FiveTransitive.Degree36ThreeOrbitGeometry
public import CFSG.Permutation.FiveTransitive.Degree36SylowThreeFiveLift

public section

namespace CFSG

namespace FiveTransitive.Degree36SylowThreeStructure

open MulAction SylowFixedActionCore

theorem orbit_card_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1)
    (x : X) (hx : x ∉ fixedPoints (sylowImage X P s S) X) :
    Nat.card (orbit (sylowImage X P s S) x) = 3 := by
  let Q := sylowImage X P s S
  obtain ⟨hF,_,_⟩ := Degree36SmallPrimeEntrance.three_entrance P hcard h5 hnotAlt s hs S hS
  have hfixeq : (sylowFixedPoints X P s S : Set X) = fixedPoints Q X :=
    FixedNormalizerAction.fixed_eq Q
  have hfixed : Nat.card (fixedPoints Q X) = 6 := by rw [← hfixeq]; exact hF
  obtain ⟨g,hg,_⟩ := Degree36SylowThreeFiveLift.exists_five P hcard h5 hnotAlt s hs S hS
  exact Degree36ThreeOrbitGeometry.orbit_card_three P hcard h5 hnotAlt Q
    (S.isPGroup'.map (fixingSubgroup P s).subtype) hfixed g hg x hx

end FiveTransitive.Degree36SylowThreeStructure

end CFSG
