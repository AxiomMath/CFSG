module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGFive
public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputsModel
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGFixLocal

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem ggL45Inputs_of_known (hsub : GGNbrSubcomponentInput) (hraw : GGRawInnFieldInput)
    (hisoI : GGRawInndiagIsoInput) (hgr : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three)
    (hcD4 : GGL45CyclicD4IOneInput) (hSchur : GGTriD4SchurInput)
    (hComp : GGTriD4ComponentsInput) (hStdL : GGTriD4StdSubInput) (hE6 : GGTwE6LocalRankInput)
    (hT : GGStdSubNotTorsionInput) (hK : GGL45KnownForms) :
    GGL45TorusIOneInput ∧ GGL45RankXAbsIOneInput ∧ GGL45FiveRankInput := by
  have hnone := ggL44iiiTriD4NoneInput_of_model hsub hSchur hComp hStdL hE6
  have hD4 := ggL45D4BstarProperInput_of_fixLocal hraw hisoI hgr ggD4FieldFixLocalOddInput_holds
  exact ⟨ggL45TorusIOneInput_of_known hraw hisoI hsub hgr hD4 hnone hStdL hE6 hT hK,
    ggL45RankXAbsIOneInput_of_known hraw hisoI hsub hgr hD4 hnone hStdL hE6 hT hK,
    ggL45FiveRankInput_of_known hraw hisoI hsub hpc hcD4 hgr hD4 hnone hStdL hE6 hT hK⟩

end CFSG.StandardType
