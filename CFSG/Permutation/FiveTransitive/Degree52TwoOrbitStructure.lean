module

public import CFSG.Permutation.FiveTransitive.Degree52TwoOrbitGeometry
public import CFSG.Permutation.FiveTransitive.Degree52TwoOrbitFiveLift

public section

namespace CFSG

namespace FiveTransitive.Degree52TwoOrbitStructure

open MulAction SylowFixedActionCore NormalizerOrbitFamily

theorem orbit_geometry
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    (∀ O : orbitRel.Quotient (sylowImage X P s S) X, Nat.card O.orbit = 1 ∨
      Nat.card O.orbit = 2 ∨ Nat.card O.orbit = 4 ∨ Nat.card O.orbit = 16) ∧
    Nat.card (Family (X := X) (sylowImage X P s S) 16) = 1 ∧
    ((Nat.card (Family (X := X) (sylowImage X P s S) 2) = 15 ∧
      Nat.card (Family (X := X) (sylowImage X P s S) 4) = 0) ∨
     (Nat.card (Family (X := X) (sylowImage X P s S) 2) = 5 ∧
      Nat.card (Family (X := X) (sylowImage X P s S) 4) = 5)) := by
  let Q := sylowImage X P s S
  have hQ : IsPGroup 2 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hX : Nat.card X = 52 := by rwa [Nat.card_eq_fintype_card]
  have hfixed : Nat.card (fixedPoints Q X) = 6 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact (Degree52TwoEntrance.fixed_six_and_image P hcard h5 hnotAlt s hs S).1
  obtain ⟨g,hg,hsingle⟩ :=
    Degree52TwoOrbitFiveLift.exists_five_unique_exterior P hcard h5 hnotAlt s hs S
  exact Degree52TwoOrbitGeometry.orbit_geometry hX Q hQ hfixed g
    (hg ▸ pow_orderOf_eq_one g) hsingle

end FiveTransitive.Degree52TwoOrbitStructure

end CFSG
