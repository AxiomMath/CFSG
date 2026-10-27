module

public import CFSG.RankThree.GF2n.Smith81.S81KWalks

public section

namespace CFSG.RankThree.GF2n.Smith81.SK


theorem lamClassList_holds : LamClassListStatement :=
  lamClassList_of_helpers lamCascadeProd_holds lamTorusNormalize_holds lamFrameWalk_holds

theorem e4InvolClasses_holds : E4InvolClassesStatement :=
  e4InvolClasses_of_lam lamClassList_holds

end CFSG.RankThree.GF2n.Smith81.SK
