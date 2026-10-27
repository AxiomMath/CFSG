module

public import CFSG.RankThree.PartTwo.Sec8.HeringU38Pair

public section

namespace CFSG.RankThree.PartTwo.Sec8


theorem kF87UBComm_holds (h45 : Sec4.Item4_5) (hM : U38SylModel) : KF87UBComm :=
  kF87UBComm_of h45 hM

theorem pair87UnitarySyl_holds
    (h45 : Sec4.Item4_5) (h49 : Sec4.Item4_9) (hM : U38SylModel) (hP : U38P3Model) :
    Pair87UnitarySyl :=
  pair87UnitarySyl_of h45 h49 hM hP

end CFSG.RankThree.PartTwo.Sec8
