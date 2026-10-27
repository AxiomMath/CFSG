module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.PrimeTwo
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.FaithfulSimple

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem

theorem solvableRankOneTheorem_of_twoThreeCase
    (htt : ∀ p : ℕ, p.Prime → 5 ≤ p → Solvable.TwoThreeCase p 1) : SolvableRankOneTheorem := by
  intro p hp
  by_cases h3 : p ≤ 3
  · exact Solvable.solvableRankOneTheoremAt_of_le_three p hp h3
  · have h4 : p ≠ 4 := fun h => by
      rw [h] at hp
      norm_num at hp
    exact Solvable.solvableRankOneTheoremAt_of_cases p hp (Solvable.fiveCase p 1 hp)
      (htt p hp (by omega))

theorem mcBrideRankOneTheorem_of
    (hcomplete : ∀ p : ℕ, p.Prime → 3 ≤ p → McBrideCompletenessAt p)
    (hsimple : ∀ p : ℕ, p.Prime → 3 ≤ p → NoFaithfulKStarSimpleAt p) : McBrideRankOneTheorem := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2
    exact mcBrideRankOneTheoremAt_two
  · have h3 : 3 ≤ p := by
      have := hp.two_le
      omega
    exact mcBrideRankOneTheoremAt_of p hp (hcomplete p hp h3)
      (faithfulSectionExclusionAt_of p hp (hsimple p hp h3))

end CFSG.SignalizerFunctorTheorem
