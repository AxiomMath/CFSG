module

public import CFSG.Permutation.FiveTransitive.OyamaOrbitDichotomy
public import CFSG.Permutation.FiveTransitive.OyamaThreeOrbitDivisibility

public section

namespace CFSG

namespace FiveTransitive.OyamaConditionFourTransitive

open MulAction

theorem four_transitive
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) : IsMultiplyPretransitive G X 4 := by
  rcases OyamaOrbitDichotomy.four_transitive_or_three_orbits hcond with h4|hthree
  · exact h4
  · exact (OyamaThreeOrbitDivisibility.contradiction hcond hthree).elim

end FiveTransitive.OyamaConditionFourTransitive

end CFSG
