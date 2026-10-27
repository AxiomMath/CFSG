module

public import CFSG.Permutation.FiveTransitive.FrobeniusCycleMoments
public import CFSG.Permutation.FiveTransitive.FourCycleMomentArithmetic

public section

namespace CFSG

namespace FiveTransitive.OyamaFourCycleOrbitCount

open MulAction Equiv FrobeniusCycleMoments

theorem orbit_counts
    (G X : Type*) [Group G] [Fintype G] [Fintype X] [MulAction G X]
    (h4 : IsMultiplyPretransitive G X 4) (hn : 4 ≤ Fintype.card X)
    (hshape : ∀ g : G, c4 (toPerm g : Perm X) ≠ 0 →
      c2 (toPerm g : Perm X) = 2 ∨ c2 (toPerm g : Perm X) = 4)
    (htwo : ∃ g : G, 0 < c4 (toPerm g : Perm X) ∧ c2 (toPerm g : Perm X) = 2)
    (hfour : ∃ g : G, 0 < c4 (toPerm g : Perm X) ∧ c2 (toPerm g : Perm X) = 4) :
    Nat.card (orbitRel.Quotient G (FrobeniusCyclePattern.admissible
      (G := G) (X := X) CyclePatternFinite.fourTwo)) = 3 ∧
    Nat.card (orbitRel.Quotient G (FrobeniusCyclePattern.admissible
      (G := G) (X := X) CyclePatternFinite.fourTwoTwo)) = 4 := by
  apply FourCycleMomentArithmetic.six_and_eight_pattern_orbits
    (fun g : G => c4 (toPerm g : Perm X)) (fun g : G => c2 (toPerm g : Perm X))
    (Nat.card G) _ _ (Nat.card_pos) hshape htwo hfour
  · exact sum_four h4 hn
  · exact sum_four_two
  · exact sum_four_two_two

end FiveTransitive.OyamaFourCycleOrbitCount

end CFSG
