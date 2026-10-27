module

public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootCountClassical
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootCountOmega
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootCountExc

public section

namespace CFSG.StandardType

theorem ggRootInvolCountTag_holds (t : CFSG.Open.StatedLieTag) : GGRootInvolCountTag t := by
  cases t with
  | PSL => exact ggRootInvolCountTag_PSL
  | PSU => exact ggRootInvolCountTag_PSU
  | PSp => exact ggRootInvolCountTag_PSp
  | POmegaOdd => exact ggRootInvolCountTag_POmegaOdd
  | POmegaPlus => exact ggRootInvolCountTag_POmegaPlus
  | POmegaMinus => exact ggRootInvolCountTag_POmegaMinus
  | F4 => exact ggRootInvolCountTag_F4
  | E6 => exact ggRootInvolCountTag_E6
  | E7 => exact ggRootInvolCountTag_E7
  | E8 => exact ggRootInvolCountTag_E8
  | twistedE6 => exact ggRootInvolCountTag_twistedE6
  | G2 => exact ggRootInvolCountTag_of_placeholder _ (by simp)
  | trialityD4 => exact ggRootInvolCountTag_of_placeholder _ (by simp)
  | twistedB2 => exact ggRootInvolCountTag_of_placeholder _ (by simp)
  | twistedG2 => exact ggRootInvolCountTag_of_placeholder _ (by simp)
  | twistedF4 => exact ggRootInvolCountTag_of_placeholder _ (by simp)
  | Tits => exact ggRootInvolCountTag_of_placeholder _ (by simp)

end CFSG.StandardType
