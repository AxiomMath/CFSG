module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieF4Main
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieBridge

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem lieF4Even :
    LieF4Even := fun n =>
  noOddConfigQ_of_noOddCfg (isoInvariant_ree .twistedF4 2 n) (f4Even_simple n)

end CFSG.Quasithin.H13.NQCore
