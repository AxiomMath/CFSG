module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableB
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLRound

public section

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG.StandardType

@[expose] def GGRemainderTableBL : Prop :=
  GGTableBCxInputOn GGCorFourTwoOpenTableBRound12Label ∧
    GGTableBModuleInputOn GGCorFourTwoOpenTableBRound12Label ∧
    GGTableBActionInputOn GGCorFourTwoOpenTableBRound12Label ∧
    GGBstarInnerDiagLInputOn GGCorFourTwoOpenLIDRound12Label ∧
    GGLTransvectionCenterInputOn GGCorFourTwoOpenTvRound12Label ∧
    GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRound12Label

end CFSG.Yardstones.M3f9567aba59d

end
