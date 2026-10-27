module

public import CFSG.Quasithin.Background.ONanE68RankOne
public import CFSG.Quasithin.Background.ONanE68Lin3
public import CFSG.Quasithin.Background.ONanE68Sp4

public section

namespace CFSG.Quasithin.E6.E68Proof

theorem e68LieFacts_holds :
    E68LieFacts where
  rankOne := e68RankOneData_holds
  lin3 := e68Lin3Data_holds
  sp4 := e68Sp4Data_holds
  psl25 := e68PSL25_holds

end CFSG.Quasithin.E6.E68Proof
