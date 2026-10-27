module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6SplitSylow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggKGTwE6InputSplit_four
    :
    GGKGTwE6InputSplit 4 :=
  fun _ _ _ σ _ _ hp hp5 hK hσ hpq => ExcTwE6Split.twE6SCTorusInput_split σ hp hp5 hK hσ hpq

end CFSG.StandardType

end
