module

public import CFSG.Permutation.FiveTransitive.Degree80SevenFixed

public section

namespace CFSG

namespace FiveTransitive.Degree80SevenCount
open MulAction SylowFixedActionCore NormalizerOrbitFamily

theorem seven_family_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card (Family (X := X) (sylowImage X P s S) 7) = 10 := by
  classical
  let Q := sylowImage X P s S
  have hsize (O : orbitRel.Quotient Q X) : Nat.card O.orbit = 1 ∨ Nat.card O.orbit = 7 := by
    refine Quotient.inductionOn O ?_
    intro x
    rw [orbitRel.Quotient.orbit_mk]
    by_cases hx : x ∈ fixedPoints Q X
    · left
      rw [Nat.card_eq_fintype_card]
      exact mem_fixedPoints_iff_card_orbit_eq_one.mp hx
    · exact Or.inr (Degree80SevenOrbits.exterior_orbit_card_seven P hcard h5 hnotAlt s hs S hS x hx)
  have hcommon : Nat.card (fixedPoints Q X) = 10 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact (Degree80SevenFixed.fixed_card_and_alternating P hcard h5 hnotAlt s hs S hS).1
  have hm := Degree80SevenOrbits.card_eq_fixed_add_seven_mul_family Q hsize
  rw [Nat.card_eq_fintype_card (α := X),hcard,hcommon] at hm
  change Nat.card (Family (X := X) Q 7) = 10
  omega

end FiveTransitive.Degree80SevenCount

end CFSG
