module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3EMain
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieBridge

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Assembly.LowTwoRank

theorem liePsl3Even : LiePsl3Even := fun n =>
  noOddConfigQ_of_noOddCfg (isoInvariant_stated .PSL 3 2 n) (psl3Even_simple n)

end CFSG.Quasithin.H13.NQCore
