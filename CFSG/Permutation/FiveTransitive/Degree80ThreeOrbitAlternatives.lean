module

public import CFSG.Permutation.FiveTransitive.Degree80ThreeOrbitMass
public import CFSG.Permutation.FiveTransitive.Degree80ThreeFixed

public section

namespace CFSG

namespace FiveTransitive.Degree80ThreeOrbitAlternatives
open MulAction SylowFixedActionCore NormalizerOrbitFamily

theorem exists_triple
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 3 (fixingSubgroup P s))
    (hS : Nat.card S ≠ 1) : ∃ x : X, Nat.card (orbit (sylowImage X P s S) x) = 3 := by
  classical
  let Q := sylowImage X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite _
  have hQ : IsPGroup 3 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hcommon : Nat.card (fixedPoints Q X) = 5 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact (Degree80ThreeFixed.three_fixed_card_and_image P hcard h5 hnotAlt s hs S hS).1
  have hm := Degree80ThreeOrbitMass.card_eq_orbit_sum (X := X)
    (by rw [Nat.card_eq_fintype_card,hcard]) Q hQ
  rw [Nat.card_eq_fintype_card (α := X),hcard,hcommon] at hm
  have hp : 0 < Nat.card (Family (X := X) Q 3) := by omega
  obtain ⟨O⟩ := (Nat.card_pos_iff.mp hp).1
  refine ⟨O.val.out,?_⟩
  have he := O.property
  rwa [orbitRel.Quotient.orbit_eq_orbit_out O.val Quotient.out_eq'] at he

end FiveTransitive.Degree80ThreeOrbitAlternatives

end CFSG
