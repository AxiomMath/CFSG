module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmall6
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmallOmega

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall6

theorem caseIISix_holds : CaseIISix :=
  fun _ _ _ _ _ C D _ hRsyl hRab hcard hI _ hgM hTM =>
    RSmall.false_of_caseII C D (le_refl 6) hRsyl hRab hI hgM hTM hcard

end CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall6
