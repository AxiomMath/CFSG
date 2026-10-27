module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
public import CFSG.LocalAnalysis.UniquenessCase.UC22Main6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] [Finite G]

structure Global22d : Prop extends Global22b where
  excFacts : UC22P20gExcFacts

end CFSG.LocalAnalysis.UniquenessCase.UC22
