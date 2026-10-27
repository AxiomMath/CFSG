module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2SuzNWC
public import CFSG.Sporadic.SuzRecog.Assembly
public import CFSG.Sporadic.SuzRecog.B0Gluing
public import CFSG.Sporadic.SuzRecog.B0TwistExcl
public import CFSG.Sporadic.SuzRecog.RootTwistCover
public import CFSG.Sporadic.SuzRecog.SuzLeaf
public import CFSG.Sporadic.SuzRecog.MixedCell
public import CFSG.Sporadic.SuzOddCore.SmallActionData

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog

theorem suzRecognition'_holds :
    CFSG.ComponentClassification.AS81.SuzRecognition' :=
  suzRecognition'_of_levelTwoGluing
    (suzLevelTwoGluing_of_leaf B0Gluing.suzB0Gluing MixedCell.mixedCellDichotomy rootTwistTrivial'
      b0TwistExcluded)

end CFSG.Sporadic.SuzRecog
