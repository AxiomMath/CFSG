module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6Sylow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggKGTwE6InputNonsplit_five
    :
    GGKGTwE6InputNonsplit 5 :=
  fun _ _ _ σ _ _ hp hp5 hK hσ hpq => ExcTwE6Nons.twE6SCTorusInput_nonsplit σ hp hp5 hK hσ hpq

end CFSG.StandardType

end
