module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieD4Main
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieBridge

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem lieD4Even :
    LieD4Even := fun n =>
  noOddConfigQ_of_noOddCfg (isoInvariant_chevalley .trialityD4 2 n) (d4Even_simple n)

end CFSG.Quasithin.H13.NQCore
