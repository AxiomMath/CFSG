module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesJ1
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate715001
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate13657
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeLeaves
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcAssembly
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcCaseV
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcTw
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcClassE6
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFAssembly
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSL
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierA1
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSU
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSpF4
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSpB2
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSpinPlus
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierTwoD
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCoverPairTwoD
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePinnedTransfer
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNCNoSU3
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNCNoB2
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNCStdEnvelope
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNCF4Envelope
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCoverPairA1
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCoverPairSL
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCoverPairSU
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairD
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairE6
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairE7
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairE8
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNCCompImage
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRelOneUse
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNCClassTransport
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNCRootGroupTwo
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGHolds
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcRelOneFive
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIncidence
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairCoreHolds
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetE6
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetE7
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCoverPairTriD4
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeShapeLeaves
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwE6
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetTwE6
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetTriD4Holds
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesF8
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesI1
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesI2
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesZ7

public section

namespace CFSG.StandardType.RCKC1

open CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKK1II
open CFSG.Open (StatedLieTag)

theorem ggSixRootCommKnownLeavesI2_of_j1
    (h : GGSixRootCommKnownLeavesJ1) : GGSixRootCommKnownLeavesI2 := by
  have hK2III : RCKRowK2IIIAtTwoRemaining := h
  have hNbr : RCKRP.RCKExcCaseVNbr := RCKRP.rckExcCaseVNbr_holds
  have hR1 : RCKRP.RCKExcRelOneAt GGExcFive := RCKRP.rckExcRelOneAt_five
  have hD : RCKRP.RCKExcReturnModelAt :=
    RCKRP.rckExcReturnModelAt_of_shape_leaves
      RCKRP.rckCarrierSL_holds RCKRP.rckCarrierA1_holds RCKRP.rckCarrierSU_holds
      RCKRP.rckCarrierSpF4_holds RCKRP.rckCarrierSpB2_holds RCKRP.rckCarrierSpinPlus_holds
      RCKRP.rckCarrierTwoD_holds RCKRP.rckPinnedOfFrameCover_holds RCKRP.rckNoSmallSU3_holds
      RCKRP.rckNoSmallB2_holds RCKRP.rckStdEnvelope_holds RCKRP.rckF4Envelope_holds
      RCKRP.rckRetE6_holds RCKRP.rckRetTwE6_holds RCKRP.rckRetE7_holds RCKRP.rckRetTriD4_holds
      RCKRP.rckPairA1_holds RCKRP.rckPairSLInner_holds RCKRP.rckPairSU_holds
      RCKRP.rckPairDInner_holds RCKRP.rckPairTwoD_holds RCKRP.rckPairE6_holds RCKRP.rckPairE7_holds
      RCKRP.rckPairE8_holds RCKRP.rckPairTwE6_holds RCKRP.rckPairTriD4_holds
      (RCKRP.rckFrameIncidence_of_pairCore RCKRP.rckFramePairCore_holds)
      RCKRP.rckCompImage_holds RCKRP.rckRelOneUse_holds RCKRP.rckClassTransport_holds
      RCKRP.rckRootGroupTwo_holds RCKRP.rckIntrinsicRoot_holds
  exact ⟨RCKRP.rckRPAt_exceptional_of RCKRP.rckLemmaF_holds (RCKRP.rck_exc_toral_of hR1 hD)
      RCKRP.rckExcCaseVReduction_holds hNbr, RCKRP.rckRPIIAt_exceptional_of RCKRP.rckLemmaFII_holds
      (RCKRP.rck_exc_toralII_of hR1 hD) RCKRP.rckExcCaseVReduction_holds hNbr, hK2III⟩

theorem rckCarrierPairADE_of_j1
    (h : GGSixRootCommKnownLeavesJ1) : RCKRP.RCKCarrierPairADE := by
  exact RCKRP.rckCarrierPairADE_of_shapes RCKRP.rckPairA1_holds RCKRP.rckPairSLInner_holds
    RCKRP.rckPairSU_holds RCKRP.rckPairDInner_holds RCKRP.rckPairTwoD_holds RCKRP.rckPairE6_holds
    RCKRP.rckPairE7_holds RCKRP.rckPairE8_holds RCKRP.rckPairTwE6_holds RCKRP.rckPairTriD4_holds

end CFSG.StandardType.RCKC1
