module

public import CFSG.LocalAnalysis.StandardType.GGTableBExc
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionE8

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


namespace TableBExcTwo

theorem ggEndNode_E7Two_holds {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    GGEndNode 3 6 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) :=
  ggEndNode_E7Two ggE7TwoRootFusionInput_holds hK


theorem ggEndNode_E8Two_holds {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    GGEndNode 3 7 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) :=
  ggEndNode_E8Two ggE8TwoRootFusionInput_holds hK

end TableBExcTwo


theorem largeEvenLabelAll_endNode_E7E8Two_holds {lab : LargeEvenLabel}
    (htag : lab.tag = .E7 ∨ lab.tag = .E8) (hn : lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift 3 r R ∧ GGEndNode 3 r R I :=
  largeEvenLabelAll_endNode_E7E8Two ggE7TwoRootFusionInput_holds ggE8TwoRootFusionInput_holds
    htag hn

theorem ggStdSubPreInputOn_E7E8Two_holds : GGStdSubPreInputOn GGTableBExcTwoLabel :=
  ggStdSubPreInputOn_E7E8Two ggE7TwoRootFusionInput_holds ggE8TwoRootFusionInput_holds

theorem ggStdSubPreInputOn_E7E8_all_holds : GGStdSubPreInputOn GGTableBE7E8AllLabel :=
  ggStdSubPreInputOn_E7E8_all ggE7TwoRootFusionInput_holds ggE8TwoRootFusionInput_holds

theorem ggStdSubPreInputOn_of_notE7E8All_holds {S : ℕ → LargeEvenLabel → Prop}
    (h : GGStdSubPreInputOn fun p lab => S p lab ∧ ¬ GGTableBE7E8AllLabel p lab) :
    GGStdSubPreInputOn S :=
  ggStdSubPreInputOn_of_notE7E8All ggE7TwoRootFusionInput_holds ggE8TwoRootFusionInput_holds h

end CFSG.StandardType
