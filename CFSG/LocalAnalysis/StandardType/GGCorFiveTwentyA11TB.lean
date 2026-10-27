module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyA11Lift
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyA11TBData

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Certs

theorem ggCorFiveTwentyA11CfgTBInput_of_mp (hMp : GGInnerDiagMpInput) :
    GGCorFiveTwentyA11CfgTBInput := by
  intro G _ _ p B Bs x L D J hHyp _ hA _
  obtain ⟨φ, hrange, hker, hdiag, hJ⟩ := GGSecFiveA11Config.exists_lift_lowerBlock hMp hHyp hA
  obtain ⟨rfl, -⟩ := hA
  have hcfg := hHyp.1
  have hx : x ≠ 1 := by
    intro h
    have h7 := hcfg.orderOf_x
    rw [h, orderOf_one] at h7
    exact absurd h7 (by norm_num)
  exact ggExcReflTBData_of_slFourLift hcfg.2.1.2.1 hcfg.2.1.2.2.2 hcfg.bstar_inf_centralizer_L hx
    φ hrange hker hdiag hJ

end Certs

end CFSG.StandardType

end
