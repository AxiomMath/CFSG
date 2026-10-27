module

public import CFSG.Permutation.FiveTransitive.Degree54TwoOrbitGeometry
public import CFSG.Permutation.FiveTransitive.Degree54TwoOrbitFiveLift

public section

namespace CFSG

namespace FiveTransitive.Degree54TwoOrbitStructure

open MulAction SylowFixedActionCore

theorem regular_orbit_data
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    (∃ x : X, Nat.card (orbit (sylowImage X P s S) x) = 16 ∧
      Nat.card (toPermHom (sylowImage X P s S) (orbit (sylowImage X P s S) x)).range = 16) ∧
    (∀ x : X, Nat.card (orbit (sylowImage X P s S) x) = 1 ∨
      Nat.card (orbit (sylowImage X P s S) x) = 2 ∨
      Nat.card (orbit (sylowImage X P s S) x) = 4 ∨
      Nat.card (orbit (sylowImage X P s S) x) = 16 ∨
      Nat.card (orbit (sylowImage X P s S) x) = 32) ∧
    (∀ x : X, Nat.card (orbit (sylowImage X P s S) x) = 16 →
      Nat.card (toPermHom (sylowImage X P s S) (orbit (sylowImage X P s S) x)).range = 16) := by
  let Q := sylowImage X P s S
  have hQ : IsPGroup 2 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hX : Nat.card X = 54 := by rwa [Nat.card_eq_fintype_card]
  have hQfixed : Nat.card (fixedPoints Q X) = 6 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact (Degree54TwoEntrance.fixed_six_and_image P hcard h5 hnotAlt s hs S).1
  obtain ⟨g,hg,_,hfixed⟩ := Degree54TwoOrbitFiveLift.exists_five_three_exterior P hcard h5 hnotAlt s hs S
  have hg5 : g ^ 5 = 1 := hg ▸ pow_orderOf_eq_one g
  obtain ⟨x,_,hO,himage⟩ := Degree54TwoSixteenWitness.exists_regular_sixteen hX.le Q hQ g hg5 hfixed
  refine ⟨⟨x,hO,himage⟩,?_,?_⟩
  · intro y
    simpa only [orbitRel.Quotient.orbit_mk] using
      Degree54TwoOrbitGeometry.orbit_sizes hX Q hQ hQfixed g hg5 hfixed (Quotient.mk'' y)
  · exact Degree54TwoOrbitGeometry.image_card_sixteen hX.le Q hQ g hg5 hfixed

end FiveTransitive.Degree54TwoOrbitStructure

end CFSG
