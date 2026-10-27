module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119KShare
public import CFSG.RankThree.PartTwo.Sec21.Hering2119SShared
public import Certificates.Certificate522001

public section

namespace CFSG.RankThree.PartTwo.Sec21

theorem item2119EndShare_holds : Item2119EndShare :=
  item2119EndShare_of_k Certificates.certificate522001

theorem item2119EndLoc_holds : Item2119EndLoc :=
  item2119EndLoc_of_share_holds item2119EndShare_holds

end CFSG.RankThree.PartTwo.Sec21
