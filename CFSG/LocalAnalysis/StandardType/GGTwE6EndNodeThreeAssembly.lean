module

public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeBig

public section

namespace CFSG.StandardType

section Assembly


theorem ggTwE6EndNodeThreeInput_of_rankFour (hCore : TwE6RootAs.TwE6CorootCore)
    (h4 : GGTwE6EndNodeThreeRankFour) : GGTwE6EndNodeThreeInput := by
  intro K _ _ n p hn hK hp hpq hp3
  subst hp3
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hadm
  by_cases h5 : 3 ^ 5 ≤ Nat.card A
  · exact TwE6EndNode3.endNode_of_big hCore hn hK hpq ψ hψ hker hperf hA hAI h5
  · exact h4 K n 3 hn hK hp hpq rfl L' ψ hψ hker hperf A hA hAI hr h3 (not_le.1 h5) hadm

end Assembly

end CFSG.StandardType

end
