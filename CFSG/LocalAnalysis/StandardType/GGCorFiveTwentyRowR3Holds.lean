module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRowR3Glue
public import CFSG.LocalAnalysis.StandardType.GGTwE6BigLineTransport
public import CFSG.LocalAnalysis.StandardType.GGTwE6BigLineDispatch
public import CFSG.LocalAnalysis.StandardType.GGTwE6BigThreeA2
public import CFSG.LocalAnalysis.StandardType.GGTwE6BigA4A1
public import CFSG.LocalAnalysis.StandardType.GGTwE6BigD5

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.SCFourCover
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

theorem ggCorFiveTwentyInputNbrRowR3_holds
    (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown)
    (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput) : GGCorFiveTwentyInputNbrRowR3 :=
  ggCorFiveTwentyInputNbrRowR3_of_big hRig hTCJ hL hPJ
    (ggTwE6BigLabelsKnown_of_line
      (ggTwE6BigLineLabels_of ggTwE6BigThreeA2_holds ggTwE6BigA4A1_holds ggTwE6BigD5_holds))

end CFSG.StandardType

end
