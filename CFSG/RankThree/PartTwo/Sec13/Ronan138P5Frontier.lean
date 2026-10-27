module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138P5EFCover
import CFSG.RankThree.PartTwo.Sec13.Ronan138P5R419
import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Elem
import CFSG.RankThree.PartTwo.Sec13.Ronan138P5S
import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Lx

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138P5

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Kinds

theorem step13PZeroCore_of_cover (hC : Sec4.K419UnitaryCensusCover) (h46 : Sec4.Item4_6)
    (h48 : Sec4.Item4_8) (hD4 : Sec4.Ronan148L.KF138TrialityPGUCent) : Step13PZeroCore :=
  step13PZeroCore_of_lift k13PZeroElem_holds step13PZeroS_holds (step13PZeroLx_of h48)
    (step13PZero419_of hC h46) (step13PZeroEFLift_of_cover hC h46 hD4)

end Kinds

end CFSG.RankThree.PartTwo.Sec13.Ronan138P5
