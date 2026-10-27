module

public import CFSG.RankThree.PartOne.K1510R.Final
public import CFSG.RankThree.PartOne.K159W.Lift5
public import CFSG.RankThree.PartOne.K159W.Dispatch

public section

namespace CFSG.RankThree.PartOne.K159W

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem kf159ZFiveResGen_of_gen (hZ : K1510R.KF159ZFiveGen) : K1510R.KF159ZFiveResGen := by
  intro G _ _ p A c L E h15 hF hout _ x hxE hx1 X hXx hpZ _
  exact hZ G p A c L E h15 hF hout x hxE hx1 X hXx hpZ

theorem kf159ZFiveResGen_holds
    (hbridge : TauCetiCatalogBridge)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h155 : Node155) (hMod : KFU5Mod) : K1510R.KF159ZFiveResGen :=
  kf159ZFiveResGen_of_gen
    (kf159ZFiveGen_of_weyl h155 hMod (centerWeylFive_of_griess hbridge hGA))

theorem node1510Five_of_bundleW
    (hS : SchreierFor InCatalog) (hSC : SchreierFor CFSG.Blueprint.Catalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) (hbridge : TauCetiCatalogBridge)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSLB : N143.SectionListBound) (hSeitz : CTP.SeitzResidual)
    (hMod : KFU5Mod) (hAt : KFU5At) (hFive : U5FiveInndiag)
    (h154 : Node154) (h155 : Node155) (h158 : Node158) (h158E3 : S15K.Node158E3) (h156 : KF156')
    (hR : U5E.Reinst5) : Node1510Five :=
  K1510R.node1510Five_of_bundleGen hS hSC h82 hbridge hGA hSLB hSeitz hMod hAt hFive h154 h155
    h158 h158E3 h156 hR (kf159ZFiveResGen_holds hbridge hGA h155 hMod)

end CFSG.RankThree.PartOne.K159W
