module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotUniqueFieldStep3
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotEnd

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie


theorem uniqueFieldInput2E6_holds : UniqueFieldInput2E6 := by
  intro G _ _ L f k K _ _ _ hset hf2 hk hK σ hσ e t htC ht G₀ hG₀
  have hKt := inf_centralizer_eq_zpowers_twistedE6 hset (by omega) hK hσ e htC ht
  obtain ⟨Ψ, -, -⟩ := hG₀.quotient
  exact unique_of_fieldRow_twistedE6_of_neighbourCore hset.standardSetting hf2 hk hK hσ e ht hKt
    hG₀.perfect hG₀.odd_card_center Ψ hG₀.le hG₀.neighbourCore_X_le hG₀.neighbourCore_Y_le

end CFSG.SeitzReduction.TwistedE6Pilot
