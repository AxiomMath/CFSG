module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGPDReduction
public import CFSG.LocalAnalysis.StandardType.GGPDCore

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggProjDegreeF4_holds : GGProjDegreeF4 := by
  intro K _ _ d hK A N hA hcard _ Γ _ _ C V _ _ ι φ h α hD hF4 _
  obtain ⟨M, hM, ρ, hρ, hz, hg⟩ := ggPD_reduction hA hcard hD hF4
  exact ggPD_core hK M hM ρ hρ hz hg

end CFSG.StandardType

end
