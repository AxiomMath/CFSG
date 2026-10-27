module

public import CFSG.LocalAnalysis.StandardType.GGRemStdSubResidualsULCOUS9
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6CubeNodeDefs
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E6Nodes
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5F4Defs
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC6Defs
public import Certificates.Certificate13657
public import Certificates.Certificate830101
import CFSG.LocalAnalysis.StandardType.GGE6InnerDiagBoundThreeProof
import CFSG.LocalAnalysis.StandardType.GGE7TwoRootAsProof
import CFSG.LocalAnalysis.StandardType.GGE8TwoRootAsProof
import CFSG.LocalAnalysis.StandardType.GGF4TwoRootAsProof
import CFSG.LocalAnalysis.StandardType.GGTwE6FieldInnerDiag
import CFSG.LocalAnalysis.StandardType.GGTwE6FieldCentInv
import CFSG.LocalAnalysis.StandardType.GGTwE6FieldThree
import CFSG.LocalAnalysis.StandardType.GGTwE6FieldLangThree
import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsToral
import CFSG.LocalAnalysis.StandardType.GGTwE6LeviSplit
import CFSG.LocalAnalysis.StandardType.GGTwE6EnnolaSplit
import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillWeyl
import CFSG.LocalAnalysis.StandardType.GGTwE6RootKernelThree
import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Holds
import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeInner
import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeNine
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeSix
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeEnd
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeAssembly
import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsInn
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC12
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC3
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC4
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E6
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC6
import CFSG.LocalAnalysis.StandardType.GGTwE6FieldThreeFourHolds
import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeFinal
import CFSG.LocalAnalysis.StandardType.GGTwE6EnnolaUpgrade
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaSmallThree
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E6Iso
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5F4ThreeC
import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreHolds
import CFSG.LocalAnalysis.StandardType.GGTwE6EltSmallFive
import CFSG.LocalAnalysis.StandardType.GGTwE6OuterRankFourHolds
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E6D4
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5Final

public section

namespace CFSG.StandardType

open CFSG.Yardstones.M3f9567aba59d (GGRemainderStdSubTableB
  ggRemainderStdSubTableB_of_residualsULCOUS9)


theorem ggRemainderStdSubTableB_of_open (hT3N : SmallExc.GGTwE6NormSmallThreeInput)
    (hCube : SmallExc.GGTwE6CubeNodeInput) :
    GGRemainderStdSubTableB :=
  have h5 := TwE6FieldCore.subfieldLangDatumFive_holds
  have h3 := TwE6FieldCore.subfieldLangDatumThree_holds
  have h34 := TwE6FieldCore.subfieldLangDatumThreeFour_holds
  have hRK := TwE6RootKill.rootKill_of_ennolaKill_weylKill
      (TwE6RootKill.ennolaKill_of_steps TwE6RootKill.leviSplitStep_holds
          TwE6RootKill.ennolaSplitStep_holds) TwE6RootKill.weylKill_holds
  have hCore := TwE6RootAs.twE6CorootCore_holds
  ggRemainderStdSubTableB_of_residualsULCOUS9
    ⟨TwE6FieldCore.ggTwE6FieldCentInvInput_of_langDatum h5 h3 h34,
      ggTwE6ThreeDeltaTwoInput_holds, ggTwE6ThreeRootKernelInput_of_rootKill hRK,
      TwE6FieldCore.ggTwE6ThreeFieldInput_of_langDatum h5 h3 h34,
      ggTwE6EndNodeInnerInput_of_core hRK h5 hCore,
      ggTwE6EndNodeThreeInput_of_upgrade hRK h34 hCore TwE6RootAs.twE6EnnolaUpgrade_holds
        TwE6RootAs.twE6OuterRankFour_holds⟩
    ggE6InnerDiagBoundThreeInput_holds ExcRootAs.ggE7TwoRootAsInput_holds
    ExcRootAs.ggE8TwoRootAsInput_holds F4RootAs.ggF4TwoRootAsInput_holds
    (TwE6FieldCore.ggTwE6InnerDiagBound2LInput_of_langDatum h5 h3 h34)
    (TwE6RootAs.ggTwE6RootAsInnInput_of_core hRK hCore h5)
    (TwE6RootAs.ggTwE6RootAsInnThreeInput_of_core hRK hCore)
    (TwE6D3.ggTwE6DeltaInput3_of_split TwE6D3.rankFiveInn_holds TwE6D3.torusLiftNineInput_holds
      TwE6D3.torusLiftSixInput_holds (TwE6D3.endNodeInput_of_core hCore))
    (SmallExc.ggStdSubSmallInputOn_hsR_of_cases SmallExcC12.ggStdSubSmallInputOn_excSplit
      SmallExcC12.ggStdSubSmallInputOn_e6Coprime SmallExc.ggStdSubSmallInputOn_e6Three
      SmallExc.ggStdSubSmallInputOn_excField
      (SmallExc.ggStdSubSmallInputOn_excTwoThree
        (SmallExc.ggE6TwoNormSmallInput_of_nodes SmallExc.E6Node.ggE6TwoD4NodeInput_holds
          SmallExc.E6Node.ggE6TwoIsoNodeInput_holds)
        SmallExc.ggE7TwoNormSmallInput_holds SmallExc.ggE8TwoNormSmallInput_holds
        SmallExc.F4Two.ggF4TwoNormSmallInput)
      (SmallExc.ggStdSubSmallInputOn_twE6 TwE6EltSmall.ggTwE6EltNormSmallInput_holds hT3N
        (SmallExc.ggTwE6DeltaSmallThreeInput_of_cube hCube)))

end CFSG.StandardType

end
