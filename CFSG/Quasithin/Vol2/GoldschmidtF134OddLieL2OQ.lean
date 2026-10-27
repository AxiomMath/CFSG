module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OL2Main
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieBridge

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Assembly.LowTwoRank

theorem liePsl2Odd : LiePsl2Odd := fun r f hr hr2 hf =>
  noOddConfigQ_of_noOddCfg (isoInvariant_stated .PSL 2 r f) (psl2Odd_simple r f hr hr2 hf)

end CFSG.Quasithin.H13.NQCore
