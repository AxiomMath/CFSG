module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check45Inputs
public meta import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check45Inputs

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS166

open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
  CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
  CFSG.Monster.B.Mathieu

@[expose] def ks166InvCheck : Bool :=
  allLt cCz.pts.size fun k =>
    let t := cCz.pts[k]!
    !(isInvolA t && eqA 315 (powArr 315 (compA 315 xArr t) 5) (idA 315)) ||
      (commA t v1Arr && commA t v2Arr)

end CFSG.RankThree.PartTwo.KFacts.KS166
