module

public import CFSG.Permutation.FiveTransitive.Degree52SevenFixedElements
public import CFSG.Permutation.FiveTransitive.Degree52ThreeSevenLift
public import CFSG.Permutation.FiveTransitive.Degree52ThreeOrbitGeometry
public import CFSG.Permutation.FiveTransitive.Degree52ThreeOrbitSharpBound

public section

namespace CFSG

namespace FiveTransitive.Degree52ThreeStructure

open MulAction SylowFixedActionCore

theorem orbit_card_three_and_bound
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    (∀ x : X, x ∉ fixedPoints (sylowImage X P s S) X →
      Nat.card (orbit (sylowImage X P s S) x) = 3) ∧ Nat.card S ≤ 243 := by
  let Q := sylowImage X P s S
  have hQ : IsPGroup 3 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  classical
  let _ : Fintype (sylowFixedPoints X P s S) := Fintype.ofFinite _
  have hF := (Degree52ThreeFixed.three_fixed_card_and_image P hcard h5 hnotAlt s hs S hS).1
  have hfixeq : (sylowFixedPoints X P s S : Set X) = fixedPoints Q X :=
    FixedNormalizerAction.fixed_eq Q
  rw [hfixeq] at hF
  obtain ⟨g,hg,hgfixed⟩ := Degree52ThreeSevenLift.exists_seven_exterior_fixed_three P hcard h5 hnotAlt
    (Degree52SevenFixedElements.fixed_card_three_or_ten P hcard h5 hnotAlt) s hs S hS
  have horbit : ∀ x : X, x ∉ fixedPoints Q X → Nat.card (orbit Q x) = 3 := by
    intro x hx
    exact Degree52ThreeOrbitGeometry.orbit_card_three_of_fixed_difference
      (by rwa [Nat.card_eq_fintype_card]) Q hQ hF g hg hgfixed x hx
  have hb := Degree52ThreeOrbitSharpBound.card_le_243 P hcard h5 hnotAlt Q hQ hF horbit
  exact ⟨horbit,by rwa [hQcard] at hb⟩

end FiveTransitive.Degree52ThreeStructure

end CFSG
