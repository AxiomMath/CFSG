module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc9R
public import CFSG.LocalAnalysis.StandardType.GGE6InnerDiagBoundThreeProof
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeSCFourOdd
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6RankFive
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusHolds
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBHalf
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelInputs
public import CFSG.LocalAnalysis.StandardType.GGF4TwoNTMain
public import CFSG.LocalAnalysis.StandardType.GGTBFixTableB
public import CFSG.LocalAnalysis.StandardType.GGTwF4SUThreeRank
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsBoth
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
public import CFSG.LocalAnalysis.StandardType.GGF4TwoThreeCCentHolds
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldInnerDiag
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsToral
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldLangThree
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldThreeFourHolds

public section

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.TableBF4TwoTB
  CFSG.LieType.SeitzGeneration.ExcHighThree

theorem ggRemainderTableBL_of_exc11r
    (hmodel : GGE6ThreeModelInput) (hR4 : GGTwE6ThreeSCFourNotTwoLocalOddInput)
    (hcent : GGF4TwoThreeCCentInput) (hX : GGTwE6InnerDiagBound2LInput) :
    GGRemainderTableBL := by
  obtain ⟨hKT, hKM, hKA, hKV, hTN, hTM, hTT, hTA, hO⟩ := ggYS203Inputs_of_model hmodel
  exact ggRemainderTableBL_of_exc9r hO (F4TwoNonToral.ggF4TwoNonToralSolvInput_of_cent hcent) hX
      ggE6InnerDiagBoundThreeInput_holds ggTwE6TorusModelInput_holds ggTwE6NoTransvectionInput_holds
      hKT hKM hKA hKV TableBExcTwoTB.ggE7TwoSCToralInput_holds
      TableBExcTwoTB.ggE8TwoSCToralInput_holds
      (ggTwE6ThreeBstarRankInput_of_known (ggTwE6ThreeSCFourNotTwoLocalInput_of_odd hR4)) hTN hTM
      hTA hTT

end CFSG.Yardstones.M3f9567aba59d

namespace CFSG.StandardType

open CFSG.Yardstones.M3f9567aba59d

theorem ggTBFixInput_holds :
    GGTBFixInput := by
  have h03 : GGRemainderTableBL :=
    ggRemainderTableBL_of_exc11r E6ThreeModel.e6ThreeModel_holds
      ggTwE6ThreeSCFourNotTwoLocalOddInput_holds
      SmallExc.F4Two.ggF4TwoThreeCCentInput_holds
      (TwE6FieldCore.ggTwE6InnerDiagBound2LInput_of_langDatum
        TwE6FieldCore.subfieldLangDatumFive_holds
        TwE6FieldCore.subfieldLangDatumThree_holds
        TwE6FieldCore.subfieldLangDatumThreeFour_holds)
  obtain ⟨-, hTBM, hTBA, -, -, -⟩ := h03
  exact ggTBFixInput_of_round12 TwF4SUThree.ggTwF4ThreeRankInput_holds hTBM hTBA

end CFSG.StandardType

end
