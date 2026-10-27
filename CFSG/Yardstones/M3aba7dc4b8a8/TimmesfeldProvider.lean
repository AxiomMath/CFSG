module

public import CFSG.LargeExtraspecial.BridgeConclusion
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Yardstones.M3aba7dc4b8a8

@[expose] def TimmesfeldPrintedStatement : Prop :=
  CFSG.LargeExtraspecial.Bridge.PrintedMainStatement

theorem timmesfeldMainStatement_of_printedStatement (hypothesis : TimmesfeldPrintedStatement) :
    CFSG.LargeExtraspecial.Bridge.MainStatement := by
  intro G group finite simple nonabelian z involution extraspecial width cardinality
    quotientModel quotientGroup quotientIso
  exact CFSG.LargeExtraspecial.Bridge.TimmesfeldPrintedConclusion.to_legacy
    (hypothesis G nonabelian z involution extraspecial width cardinality quotientModel quotientIso)

end CFSG.Yardstones.M3aba7dc4b8a8
