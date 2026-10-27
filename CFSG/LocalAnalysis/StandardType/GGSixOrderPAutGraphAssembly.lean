module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSL
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutGraphExc
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutGraphSp
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutGraphSU
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutGraphTwE6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

section Assembly

theorem ggOrdPGraphAt_of_orthogonal (hP : GGOrdPGraphAt .POmegaPlus)
    (hM : GGOrdPGraphAt .POmegaMinus) : ∀ t, GGOrdPGraphAt t := by
  intro t
  cases t with
  | PSL => exact ggOrdPGraphAt_PSL
  | PSU => exact ggOrdPGraphAt_PSU
  | PSp => exact ggOrdPGraphAt_PSp
  | POmegaOdd => exact ggOrdPGraphAt_of_small (by simp [GGOrdPSmallTag])
  | POmegaPlus => exact hP
  | POmegaMinus => exact hM
  | G2 => exact ggOrdPGraphAt_of_small (by simp [GGOrdPSmallTag])
  | F4 => exact ggOrdPGraphAt_F4
  | E6 => exact ggOrdPGraphAt_E6
  | E7 => exact ggOrdPGraphAt_E7
  | E8 => exact ggOrdPGraphAt_E8
  | twistedE6 => exact ggOrdPGraphAt_twistedE6
  | trialityD4 => exact ggOrdPGraphAt_of_small (by simp [GGOrdPSmallTag])
  | twistedB2 => exact ggOrdPGraphAt_of_small (by simp [GGOrdPSmallTag])
  | twistedG2 => exact ggOrdPGraphAt_of_small (by simp [GGOrdPSmallTag])
  | twistedF4 => exact ggOrdPGraphAt_of_small (by simp [GGOrdPSmallTag])
  | Tits => exact ggOrdPGraphAt_of_small (by simp [GGOrdPSmallTag])

theorem ggSixLSixElevenKGInput_of_rest_orth (h1 : ∀ t, ¬ GGOrdPSmallTag t → GGOrdPInnerConjAt t)
    (h2 : ∀ t, ¬ GGOrdPSmallTag t → GGOrdPFieldConjAt t)
    (h3 : ∀ t, (t = .PSL ∨ t = .PSU ∨ t = .E6 ∨ t = .twistedE6) → GGOrdPOutdiagAt t)
    (hP : GGOrdPGraphAt .POmegaPlus) (hM : GGOrdPGraphAt .POmegaMinus)
    (h5 : GGOrdPTrialityInput) : GGSixLSixElevenKGInput :=
  ggSixLSixElevenKGInput_of_rest h1 h2 h3
    (fun t _ _ => ggOrdPGraphAt_of_orthogonal hP hM t) h5

theorem ggSixLSixElevenKGInput_of_rest_orth_model
    (h1 : ∀ t, ¬ GGOrdPSmallTag t → GGOrdPInnerConjAt t)
    (h2 : ∀ t, ¬ GGOrdPSmallTag t → GGOrdPFieldConjAt t)
    (h3 : ∀ t, (t = .PSL ∨ t = .PSU ∨ t = .E6 ∨ t = .twistedE6) → GGOrdPOutdiagAt t)
    (hP : GGOrdPGraphModelAt .POmegaPlus) (hM : GGOrdPGraphModelAt .POmegaMinus)
    (h5 : GGOrdPTrialityInput) : GGSixLSixElevenKGInput :=
  ggSixLSixElevenKGInput_of_rest_orth h1 h2 h3 (ggOrdPGraphAt_of_model hP)
    (ggOrdPGraphAt_of_model hM) h5

end Assembly

end CFSG.StandardType
