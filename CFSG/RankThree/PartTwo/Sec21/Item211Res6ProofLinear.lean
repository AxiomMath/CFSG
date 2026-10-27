module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofGraph

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open Item211Res6Proof

theorem ks211L3OuterCentLinear_holds : KS211L3OuterCentLinear := by
  intro K _ _ p _ _ hp3 hK3 D T hDe hD9 hT2 _ hTD hnab _
  change OuterCentConcl (innP K) T
  by_cases hR : T ⊓ innP K = ⊥
  · by_cases hsemi : ∀ t ∈ T, t ∈ semilinearAutGroup 3 K
    · exact outerCentConcl_of_semilinear hp3 hT2 hR hsemi
    · push Not at hsemi
      obtain ⟨t₀, ht₀, ht₀s⟩ := hsemi
      exact outerCentConcl_of_not_semilinear hp3 hT2 hR ht₀ ht₀s
  · exact outerCentConcl_of_inf_ne_bot hp3 hK3 hDe hD9 hT2 hTD hnab hR

theorem ks211L3PlusLinearOuter_holds : KS211L3PlusLinearOuter :=
  ks211L3PlusLinearOuter_of_cent ks211L3OuterCentLinear_holds

end CFSG.RankThree.PartTwo.Sec21
