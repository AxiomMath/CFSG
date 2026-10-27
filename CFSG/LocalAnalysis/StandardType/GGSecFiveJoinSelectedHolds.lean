module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelected
import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelectedSpMember
import CFSG.LocalAnalysis.StandardType.GGF4JoinMemberPOmegaPlus
import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelectedOmegaMinus
import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelectedF4
import CFSG.LocalAnalysis.StandardType.GGSelectedE7Guarded
import CFSG.LocalAnalysis.StandardType.GGF4JoinMemberE8
import CFSG.LocalAnalysis.StandardType.GGF4JoinMemberTwistedE6

public section

namespace CFSG.StandardType


theorem knownActualMemberSelectedInput_holds : KnownActualMemberSelectedInput := by
  intro G _ _ p B Bs x L D J hcfg t n f ψ hpres X horigin hmark
  cases t with
  | PSL => exact ggActualMember_PSL_selected hcfg ψ hpres horigin hmark
  | PSU => exact ggActualMember_PSU_selected hcfg ψ hpres horigin hmark
  | PSp => exact ggActualMember_PSp_selected hcfg ψ hpres horigin hmark
  | POmegaPlus => exact ggActualMember_POmegaPlus_selected hcfg ψ hpres horigin hmark
  | POmegaMinus => exact ggActualMember_POmegaMinus_selected hcfg ψ hpres horigin hmark
  | F4 => exact ggActualMember_F4_selected hcfg ψ hpres horigin hmark
  | E6 => exact ggActualMember_E6_selected hcfg ψ hpres horigin hmark
  | E7 => exact ggActualMember_E7_selected hcfg ψ hpres horigin hmark
  | E8 => exact ggActualMember_E8_selected hcfg ψ hpres horigin hmark
  | twistedE6 => exact ggActualMember_twistedE6_selected hcfg ψ hpres horigin hmark
  | POmegaOdd => exact False.elim (hpres.1.1.2.2.2 rfl)
  | G2 =>
    have hrank := hpres.1.2
    change 2 ≤ 0 at hrank
    omega
  | trialityD4 =>
    have hrank := hpres.1.2
    change 2 ≤ 0 at hrank
    omega
  | twistedB2 =>
    have hrank := hpres.1.2
    change 2 ≤ 0 at hrank
    omega
  | twistedG2 =>
    have hrank := hpres.1.2
    change 2 ≤ 0 at hrank
    omega
  | twistedF4 =>
    have hrank := hpres.1.2
    change 2 ≤ 0 at hrank
    omega
  | Tits =>
    have hrank := hpres.1.2
    change 2 ≤ 0 at hrank
    omega

end CFSG.StandardType

end
