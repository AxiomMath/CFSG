module

public import CFSG.Quasithin.MS93.Burnside.Sp4HMain
public import CFSG.Quasithin.MS93.MResDefs

public section

namespace CFSG.Quasithin.MS93.S4L

theorem burnsideSp4H_noNonlinSp : NoNonlinSp :=
  noNonlinSp_of burnsideSp4H_noNonlinSp4 burnsideSp4H_noNonlinSpGt4

theorem burnsideSp4H_s34RDescSp4 : CFSG.Quasithin.MS93.MRes.S34RDescSp4 := by
  intro G _ _ M T L h hmin hb hc
  exact (burnsideSp4H_noNonlinSp G M T L h hmin hb hc.1 hc.2).elim

end CFSG.Quasithin.MS93.S4L
