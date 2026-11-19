module

public import CFSG.Permutation.FiveTransitive.CyclePatternFinite
public import CFSG.Permutation.FiveTransitive.FrobeniusCyclePattern

public section

namespace CFSG

namespace FiveTransitive.FrobeniusCycleMoments

open Equiv MulAction CyclePatternRoots
open scoped BigOperators

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [MulAction G X]

noncomputable abbrev c2 (g : Perm X) : ℕ := Nat.card (TwoRoot g)
noncomputable abbrev c4 (g : Perm X) : ℕ := Nat.card (FourRoot g)

theorem sum_four (h4 : IsMultiplyPretransitive G X 4) (hn : 4 ≤ Fintype.card X) :
    (∑ g : G, c4 (toPerm g : Perm X)) = Nat.card G := by
  have hc (g : G) :
      Nat.card {e : Fin 4 ↪ X // ∀ i, g • e i = e ((finRotate 4) i)} = c4 (toPerm g : Perm X) :=
    card_four_pattern (toPerm g : Perm X)
  have h := FrobeniusCyclePattern.sum_card_pattern_eq_card_group h4 hn (finRotate 4)
  simpa only [hc] using h

theorem sum_four_two :
    (∑ g : G, c4 (toPerm g : Perm X) * c2 (toPerm g : Perm X)) =
      Nat.card G * Nat.card (orbitRel.Quotient G
        (FrobeniusCyclePattern.admissible (G := G) (X := X) CyclePatternFinite.fourTwo)) := by
  have hc (g : G) :
      Nat.card {e : Fin 6 ↪ X // ∀ i, g • e i = e (CyclePatternFinite.fourTwo i)} =
        c4 (toPerm g : Perm X) * c2 (toPerm g : Perm X) :=
    CyclePatternFinite.card_four_two (toPerm g : Perm X)
  have h := FrobeniusCyclePattern.sum_card_pattern_eq_orbits (G := G) (X := X)
    CyclePatternFinite.fourTwo
  simpa only [hc] using h

theorem sum_four_two_two :
    (∑ g : G, c4 (toPerm g : Perm X) * c2 (toPerm g : Perm X) * (c2 (toPerm g : Perm X) - 2)) =
      Nat.card G * Nat.card (orbitRel.Quotient G
        (FrobeniusCyclePattern.admissible (G := G) (X := X) CyclePatternFinite.fourTwoTwo)) := by
  have hc (g : G) :
      Nat.card {e : Fin 8 ↪ X // ∀ i, g • e i = e (CyclePatternFinite.fourTwoTwo i)} =
        c4 (toPerm g : Perm X) * c2 (toPerm g : Perm X) * (c2 (toPerm g : Perm X) - 2) :=
    CyclePatternFinite.card_four_two_two (toPerm g : Perm X)
  have h := FrobeniusCyclePattern.sum_card_pattern_eq_orbits (G := G) (X := X)
    CyclePatternFinite.fourTwoTwo
  simpa only [hc] using h

end FiveTransitive.FrobeniusCycleMoments

end CFSG
