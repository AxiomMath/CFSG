module

public import CFSG.Permutation.FiveTransitive.OyamaFourCycleOrbitCount
public import CFSG.Permutation.FiveTransitive.TupleFiberOrbits

public section

namespace CFSG

namespace FiveTransitive.OyamaFourBaseOrbitCount

open MulAction Equiv FrobeniusCycleMoments

theorem four_orbits
    (G X : Type*) [Group G] [Fintype G] [Fintype X] [MulAction G X]
    (h4 : IsMultiplyPretransitive G X 4) (hn : 4 ≤ Fintype.card X)
    (hshape : ∀ g : G, c4 (toPerm g : Perm X) ≠ 0 →
      c2 (toPerm g : Perm X) = 2 ∨ c2 (toPerm g : Perm X) = 4)
    (htwo : ∃ g : G, 0 < c4 (toPerm g : Perm X) ∧ c2 (toPerm g : Perm X) = 2)
    (hfour : ∃ g : G, 0 < c4 (toPerm g : Perm X) ∧ c2 (toPerm g : Perm X) = 4)
    (j : Fin 4 ↪ Fin 8) (b : Fin 4 ↪ X) :
    Nat.card (orbitRel.Quotient (stabilizer G b) (TupleFiberOrbits.fiber
      (FrobeniusCyclePattern.admissible (G := G) (X := X) CyclePatternFinite.fourTwoTwo)
      j b)) = 4 := by
  rw [← TupleFiberOrbits.card_orbits_eq h4]
  exact (OyamaFourCycleOrbitCount.orbit_counts G X h4 hn hshape htwo hfour).2

end FiveTransitive.OyamaFourBaseOrbitCount

end CFSG
