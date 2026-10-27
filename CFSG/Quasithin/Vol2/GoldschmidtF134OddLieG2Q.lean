module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieG2Main
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieBridge

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem lieG2Even :
    LieG2Even := fun n =>
  noOddConfigQ_of_noOddCfg (isoInvariant_chevalley .G2 2 n) (g2Even_simple n)

end CFSG.Quasithin.H13.NQCore
