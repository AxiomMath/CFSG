module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrime
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFPSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFPOmegaMinusThree
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGHolds

public section

namespace CFSG.StandardType.RCKRP

theorem rckLemmaF_holds :
    RCKLemmaF :=
  rckLemmaF_of_at fun t ht => by
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact rckLemmaFAt_PSL rckIntrinsicRoot_holds
    · exact rckLemmaFAt_PSU rckIntrinsicRoot_holds
    · exact rckLemmaFAt_PSp rckIntrinsicRoot_holds
    · exact rckLemmaFAt_POmegaPlus rckIntrinsicRoot_holds
    · exact rckLemmaFAt_POmegaMinus_holds rckIntrinsicRoot_holds

theorem rckRPAt_classical_holds :
    RCKRPAt RCKClassicalTag :=
  rckRPAt_classical_of rckLemmaF_holds rckClassicalCompModel_holds

theorem rckLemmaFII_holds :
    RCKLemmaFII :=
  rckLemmaFII_of_at fun t ht => by
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact rckLemmaFIIAt_PSL rckIntrinsicRoot_holds
    · exact rckLemmaFIIAt_PSU rckIntrinsicRoot_holds
    · exact rckLemmaFIIAt_PSp rckIntrinsicRoot_holds
    · exact rckLemmaFIIAt_POmegaPlus rckIntrinsicRoot_holds
    · exact rckLemmaFIIAt_POmegaMinus_of_PSU rckIntrinsicRoot_holds
        (rckLemmaFIIAt_PSU rckIntrinsicRoot_holds)

theorem rckRPIIAt_classical_holds :
    RCKRPIIAt RCKClassicalTag :=
  rckRPIIAt_classical_of rckLemmaFII_holds rckClassicalCompModel_holds

end CFSG.StandardType.RCKRP
