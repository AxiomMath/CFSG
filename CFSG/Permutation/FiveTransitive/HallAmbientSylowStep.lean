module

public import CFSG.Permutation.FiveTransitive.HallSylowFromC
public import CFSG.Permutation.FiveTransitive.HallSylowFixedSet

public section

namespace CFSG

namespace FiveTransitive.Research.HallAmbientSylowStep

open MulAction
open Research.HallOrbitTransitivity
open Research.HallSylowNormalizer
open Research.HallSylowFromC
open Research.HallSylowFixedSet

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

theorem exists_ambientSylow_fixedPoints_cases
    {p : ℕ} [Fact p.Prime]
    (e : Fin 4 ↪ X) (a b : G)
    (he : ∀ i, e i ∈ exceptionalSet (X := X) a b)
    (hEcard : (exceptionalSet (X := X) a b).ncard = 6 ∨
      (exceptionalSet (X := X) a b).ncard = 7)
    (t : ℕ)
    (hcommon : ∀ x : X, x ∉ exceptionalSet (X := X) a b →
      (MulAction.orbit (hallCentralizer (X := X) a b) x).ncard = t)
    (hpdiv : p ∣ t) (hpTwo : p ≠ 2) :
    ∃ P : Sylow p (hallCentralizer (X := X) a b),
      ∃ Q : Sylow p (MulAction.stabilizer G e),
        sylowImage (hallCentralizer (X := X) a b) P ≤
            ambientSylow e Q ∧
          (MulAction.fixedPoints (ambientSylow e Q) X =
              exceptionalSet (X := X) a b ∨
            p = 3 ∧
              (exceptionalSet (X := X) a b).ncard = 7 ∧
              MulAction.fixedPoints (ambientSylow e Q) X =
                Set.range e) := by
  let C := hallCentralizer (X := X) a b
  let E := exceptionalSet (X := X) a b
  let P : Sylow p C := Sylow.nonempty.some
  have hCbase : C ≤ MulAction.stabilizer G e :=
    hallCentralizer_le_stabilizer e a b he
  obtain ⟨Q, hPQ⟩ :=
    exists_ambientSylow_containing_sylowImage e C hCbase P
  have hCfix : ∀ c : C, ∀ x ∈ E, (c : G) • x = x := by
    intro c x hx
    exact (mem_hallCentralizer_iff a b (c : G)).mp c.prop |>.1 x hx
  have hEfixed : E ⊆
      MulAction.fixedPoints (sylowImage C P) X :=
    exceptional_subset_fixedPoints_sylowImage C P E hCfix
  have horbit : ∀ x : X, x ∉ E →
      p ∣ (MulAction.orbit C x).ncard := by
    intro x hx
    rw [hcommon x hx]
    exact hpdiv
  have houtside : ∀ x : X, x ∉ E →
      ∃ z : sylowImage C P, z • x ≠ x :=
    outside_moved_by_sylowImage C P E horbit
  have hPgroup : IsPGroup p (sylowImage C P) :=
    sylowImage_isPGroup C P
  have hfixed := ambientSylow_fixedPoints_eq_exceptional_or_three
    e Q E hEcard (sylowImage C P) hPgroup hPQ hEfixed houtside hpTwo
  exact ⟨P, Q, hPQ, hfixed.2.2⟩

end FiveTransitive.Research.HallAmbientSylowStep

end CFSG
