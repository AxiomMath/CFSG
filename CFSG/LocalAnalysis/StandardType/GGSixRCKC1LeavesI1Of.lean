module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesI1
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpRecExceptional
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGHolds
import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagSpinPlusFour
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpRec
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpSLFour
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Collinear
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1CollinearTriD4
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesF8
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesZ7

public section

namespace CFSG.StandardType.RCKC1

section Certificates


theorem ggSixRootCommKnownLeavesZ7_of_i1
    (h : GGSixRootCommKnownLeavesI1) : GGSixRootCommKnownLeavesZ7 := by
  obtain ⟨h2, h3, h5, h6C⟩ := h
  have h6E : RCKIIpAt GGExcFive := rckIIpAt_excFive
  exact ⟨RCKRP.rckIntrinsicRoot_holds, h2, h3, rckK2NbrCollinear_of_rest rckCollinearRest_holds, h5,
    rckRowK2_IIp_of (rckIIpRecognition_of_at h6C h6E) rckIIpSLFourBridge rckIIpOmegaSixBridge
      rckOrthPointK2
      (CFSG.StandardType.RCKFlag.rckK2FlagRootSub_of_spinPlusFour
        CFSG.StandardType.RCKFlag.rckFlagSpinPlusFourOdd_holds)⟩

end Certificates

end CFSG.StandardType.RCKC1
