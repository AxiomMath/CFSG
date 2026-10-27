module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Main11

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] [Finite G]

structure Global22e : Prop extends Global22d where
  threeNoncentral : ThreeNoncentralFact

end CFSG.LocalAnalysis.UniquenessCase.UC22
