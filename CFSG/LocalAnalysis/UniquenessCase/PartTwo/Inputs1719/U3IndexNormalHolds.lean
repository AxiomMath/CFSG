module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenU3
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupU3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexNormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.WeakClosure81

theorem k_U3IndexNormal_holds :
    K_U3IndexNormal := by
  intro X _ _ K T H n hKH hKn _hperf _hq hU hTsyl hsup
  exact inF_top_of_inFGroup n
    (S18.inFGroupU3Setting_imageBar2 hKH hKn hU hTsyl.isPGroup hsup).inFGroup

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
