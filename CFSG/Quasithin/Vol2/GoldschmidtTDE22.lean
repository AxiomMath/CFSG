module

public import CFSG.Quasithin.Vol2.Ch5Sec1HallE22
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NNH

public section

namespace CFSG.Quasithin.H13

theorem e22BorelSolvableFact_holds : E22BorelSolvableFact :=
  fun _ _ _ _ _ _ _ hB => Sec1211Nq.isSolvable_of_isBorelIn hB

end CFSG.Quasithin.H13
