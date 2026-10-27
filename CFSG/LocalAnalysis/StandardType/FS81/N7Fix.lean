module

public import CFSG.LocalAnalysis.StandardType.FS81.N7Split
public import CFSG.LocalAnalysis.StandardType.FS81.N7FixCore
public import CFSG.LocalAnalysis.StandardType.FS81.N7FixPlumb
public import CFSG.LocalAnalysis.StandardType.FS81.GoldExclusion

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

theorem l1N7Fix_of_goldSylow (hG : GoldExclusionSylow) : L1N7Fix := by
  intro G _ _ b₀ K E _ B hB _ hfus hodd hN0
  obtain ⟨X, _, _, ⟨S⟩⟩ := N7Setup.exists_of_cases G b₀ K E B hB hfus hodd hN0
  exact n7Fix_core hG S

theorem l1N7Fix_holds :
    L1N7Fix :=
  l1N7Fix_of_goldSylow goldExclusionSylow_of_certificates

end CFSG.StandardType.FrameRoute.FS81

end
