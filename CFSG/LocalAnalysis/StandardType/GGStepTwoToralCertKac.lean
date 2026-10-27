module

public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertSpec
public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertVec

public section

namespace CFSG.StandardType.StepTwoToralCert

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem kacOf_θ_apply (τ : Tag) (i : Fin τ.rank) : (kacOf τ).θ i = tcEnt (tcTheta τ) i := by
  cases τ <;> fin_cases i <;> rfl

theorem kacOf_c_apply (τ : Tag) (i : Fin τ.rank) : (kacOf τ).c i = tcEnt (tcCoTheta τ) i := by
  cases τ <;> fin_cases i <;> rfl

theorem tcTheta_pos (τ : Tag) (i : Fin τ.rank) : 0 < tcEnt (tcTheta τ) i := by
  cases τ <;> fin_cases i <;> decide

end CFSG.StandardType.StepTwoToralCert
