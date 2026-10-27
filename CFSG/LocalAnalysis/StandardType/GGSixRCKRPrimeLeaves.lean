module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNonclassical
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeEnvelopePieces
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeShapeLeaves

public section

namespace CFSG.StandardType.RCKRP

theorem rckExcReturnModelAt_of_leaves
    (hSL : RCKCarrierSL) (hA1 : RCKCarrierA1) (hSU : RCKCarrierSU) (hSpF4 : RCKCarrierSpF4)
    (hSpB2 : RCKCarrierSpB2) (hSpin : RCKCarrierSpinPlus) (hTwoD : RCKCarrierTwoD)
    (hTrf : RCKPinnedOfFrameCover) (hNoSU3 : RCKNoSmallSU3) (hNoB2 : RCKNoSmallB2)
    (hADE : RCKStdEnvelope) (hF4 : RCKF4Envelope)
    (hRet : RCKCarrierRet) (hPair : RCKCarrierPairADE) (hInc : RCKFrameIncidence)
    (hCI : RCKCompImage) (hOne : RCKRelOneUse)
    (hTr : RCKClassTransport) (hTwo : RCKRootGroupTwo) (hIRG : RCKIntrinsicRoot) :
    RCKExcReturnModelAt :=
  rckExcReturnModelAt_of_pieces hSL hA1 hSU hSpF4 hSpB2 hSpin hTwoD hTrf
    (rckNoSmall_of_cases hNoSU3 hNoB2) (rckClassEnvelope_of_pieces hADE hF4) hRet hPair
    hInc hADE hCI hOne hTr hTwo hIRG

theorem rckExcReturnModelAt_of_shape_leaves
    (hSL : RCKCarrierSL) (hA1 : RCKCarrierA1) (hSU : RCKCarrierSU) (hSpF4 : RCKCarrierSpF4)
    (hSpB2 : RCKCarrierSpB2) (hSpin : RCKCarrierSpinPlus) (hTwoD : RCKCarrierTwoD)
    (hTrf : RCKPinnedOfFrameCover) (hNoSU3 : RCKNoSmallSU3) (hNoB2 : RCKNoSmallB2)
    (hADE : RCKStdEnvelope) (hF4 : RCKF4Envelope)
    (hR1 : RCKRetE6) (hR2 : RCKRetTwE6) (hR3 : RCKRetE7) (hR4 : RCKRetTriD4)
    (hP1 : RCKPairA1) (hP2 : RCKPairSLInner) (hP3 : RCKPairSU) (hP4 : RCKPairDInner)
    (hP5 : RCKPairTwoD) (hP6 : RCKPairE6) (hP7 : RCKPairE7) (hP8 : RCKPairE8)
    (hP9 : RCKPairTwE6) (hP10 : RCKPairTriD4)
    (hInc : RCKFrameIncidence) (hCI : RCKCompImage)
    (hOne : RCKRelOneUse) (hTr : RCKClassTransport) (hTwo : RCKRootGroupTwo)
    (hIRG : RCKIntrinsicRoot) : RCKExcReturnModelAt :=
  rckExcReturnModelAt_of_leaves hSL hA1 hSU hSpF4 hSpB2 hSpin hTwoD hTrf hNoSU3 hNoB2 hADE hF4
    (rckCarrierRet_of_shapes hR1 hR2 hR3 hR4)
    (rckCarrierPairADE_of_shapes hP1 hP2 hP3 hP4 hP5 hP6 hP7 hP8 hP9 hP10) hInc hCI hOne hTr
    hTwo hIRG

end CFSG.StandardType.RCKRP
