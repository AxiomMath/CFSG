module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureExcSmall
public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions

public section

namespace CFSG.Yardstones.Mf4cdcdf2e013

theorem Standing4.false_of_smallExceptionalTwoCase {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (h : CFSG.LocalAnalysis.RankThreeUC.SmallExceptionalTwoCase G) : False := by
  have h2 : CFSG.Assembly.evenRank G ≤ 2 :=
    CFSG.LocalAnalysis.RankThreeUC.evenRank_le_two_of_smallExceptionalTwoCase h
  have h4 : 4 ≤ CFSG.Assembly.evenRank G := hS.rank
  omega

end CFSG.Yardstones.Mf4cdcdf2e013
