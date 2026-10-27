module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeConfigID
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMPSL
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMPSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMPSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMPOmegaMinus

public section

namespace CFSG.StandardType.RCKRP


theorem rckCompModel_of_POmegaMinus (h : RCKClassicalCompModelAt .POmegaMinus) :
    RCKCompModel :=
  rckClassicalCompModel_of_at rckRPConfigInnerDiag_holds fun t ht => by
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact rckClassicalCompModelAt_PSL
    · exact rckClassicalCompModelAt_PSU
    · exact rckClassicalCompModelAt_PSp
    · exact rckClassicalCompModelAt_POmegaPlus
    · exact h

theorem rckClassicalCompModel_of_POmegaMinus (h : RCKClassicalCompModelAt .POmegaMinus) :
    RCKClassicalCompModel :=
  rckClassicalCompModel_of_comp (rckCompModel_of_POmegaMinus h)

theorem rckCompModel_holds : RCKCompModel :=
  rckCompModel_of_POmegaMinus rckClassicalCompModelAt_POmegaMinus

theorem rckClassicalCompModel_holds : RCKClassicalCompModel :=
  rckClassicalCompModel_of_POmegaMinus rckClassicalCompModelAt_POmegaMinus

end CFSG.StandardType.RCKRP
