module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieU3OMain
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieBridge

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Assembly.LowTwoRank

theorem liePsu3Odd : LiePsu3Odd := fun r hr hr2 =>
  noOddConfigQ_of_noOddCfg (isoInvariant_stated .PSU 3 r 1) (psu3Odd_simple r hr hr2)

end CFSG.Quasithin.H13.NQCore
