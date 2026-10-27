module

public import CFSG.Permutation.FiveTransitive.Degree80TwoEightBound
public import CFSG.Permutation.FiveTransitive.Degree80TwoTwelveExclusion
public import CFSG.Permutation.FiveTransitive.Degree80OrderContradiction

public section

namespace CFSG

namespace FiveTransitive.Degree80TwoResidual
open MulAction SylowFixedActionCore

private theorem fixed_six_or_eight
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    Nat.card (sylowFixedPoints X P s S) = 6 ∨
      Nat.card (sylowFixedPoints X P s S) = 8 := by
  have hc := Degree80TwoBound.fixed_card_cases P hcard h5 s hs S
  have hn := Degree80TwoTwelveExclusion.fixed_card_ne_twelve P hcard h5 hnotAlt s hs S
  omega

theorem excluded_of_six_bound
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hbound : ∀ (s : Set X), s.ncard = 5 → ∀ S : Sylow 2 (fixingSubgroup P s),
      Nat.card (sylowFixedPoints X P s S) = 6 → Nat.card S ≤ 2 ^ 16) : False := by
  apply Degree80OrderContradiction.excluded P hcard h5 hnotAlt
  intro s hs S
  rcases fixed_six_or_eight P hcard h5 hnotAlt s hs S with h6 | h8
  · exact hbound s hs S h6
  · exact (Degree80TwoEightBound.sylow_card_le_eight P hcard h5 hnotAlt s hs S h8).trans (by decide)

end FiveTransitive.Degree80TwoResidual

end CFSG
