module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LangRound
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperDefs
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreNarrow
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmall
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeLabels
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicRootCenter

public section

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG.StandardType


@[expose] def GGRemainderStdSubTableB : Prop :=
  GGTableBTwE6Round12Lang ∧
    GGStdSubIOneProperInputOn GGIOneProperRestNarrowLabel ∧
    GGStdSubSmallInputOn GGStdSubSmallRest4Label ∧
    GGLayerCenterCyclicModelRestTwo

end CFSG.Yardstones.M3f9567aba59d

end
