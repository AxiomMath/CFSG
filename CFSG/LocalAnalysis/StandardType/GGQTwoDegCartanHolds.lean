module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDegDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieCartan

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType

theorem ggCartanRankLe_holds : GGCartanRankLe :=
  fun hp hp2 hel _ ρ hinj hrefl hnotr => ggCartanRank_le hp hp2 hel ρ hinj hrefl hnotr

end CFSG.StandardType.QTwo

end
