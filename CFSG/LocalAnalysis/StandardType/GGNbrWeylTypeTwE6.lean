module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitFamilies
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeTwE6Aux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggNbrTableBWeylTypeNonSplitOn_twE6 :
    GGNbrTableBWeylTypeNonSplitOn GGNbrNonSplitTwE6Label := by
  intro p hp hp2 lab hlab hS _
  obtain ⟨ht, hplus | hminus⟩ := hS
  · exact ggWTTw_largeEvenLabelAll_weylTypeW_twE6Plus hp hp2 hplus.1 hlab ⟨ht, hplus.2⟩
  · by_cases hp3 : p = 3
    · subst hp3
      exact ggWTTw_largeEvenLabelAll_weylTypeW_twE6Three hlab ⟨ht, hminus⟩
    · have hp5 : 5 ≤ p := by
        have := hp.two_le
        have h4 : p ≠ 4 := fun h4 => by subst h4; exact absurd hp (by norm_num)
        omega
      exact TwE6Delta.labelAll ht fun K _ _ hK _ _ =>
        ⟨4, ggTorusLift_twE6Dvd_holds hlab.1 hK hp hp2 hminus,
          ggWTTw_weylTypeW_twE6Split hlab.1 hK hp hp5 hminus⟩

end CFSG.StandardType

end
