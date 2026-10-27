module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestField
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestTwisted

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Family

theorem ggSixLSixElevenKGInput_of_rest_PSL (hK1 : GGOrdPInnerConjPSLNonsplit)
    (hK2 : GGOrdPFieldConjPSLNonsplit)
    (h1 : ∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → GGOrdPInnerConjAt t)
    (h2 : ∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → GGOrdPFieldConjAt t)
    (h3 : ∀ t, (t = .PSU ∨ t = .E6 ∨ t = .twistedE6) → GGOrdPOutdiagAt t)
    (h4 : ∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → GGOrdPGraphAt t) (h5 : GGOrdPTrialityInput) :
    GGSixLSixElevenKGInput := by
  refine ggSixLSixElevenKGInput_of_rest (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) h4 h5
  · by_cases hP : t = .PSL
    · subst hP
      exact ggOrdPInnerConjAt_PSL_of_nonsplit hK1
    · exact h1 t ht hP
  · by_cases hP : t = .PSL
    · subst hP
      exact ggOrdPFieldConjAt_PSL_of_nonsplit hK2
    · exact h2 t ht hP
  · rcases ht with rfl | ht
    · exact ggOrdPOutdiagAt_PSL
    · exact h3 t ht

end Family

end CFSG.StandardType
