module

public import CFSG.Quasithin.MS93.S4L5Stmt
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Quasithin.MS93.MResDefs
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin

theorem MS93.MRes.s34FDescSp4_of_noNonlin (h4 : MS93.S4L.NoNonlinSp4)
    (hg : MS93.S4L.NoNonlinSpGt4) : MS93.MRes.S34FDescSp4 := by
  intro G _ _ M T L h hmin hb hc _ _ _ _
  exact (MS93.S4L.noNonlinSp_of h4 hg G M T L h hmin hb hc.1.isSp4U hc.2).elim

end CFSG.Quasithin
