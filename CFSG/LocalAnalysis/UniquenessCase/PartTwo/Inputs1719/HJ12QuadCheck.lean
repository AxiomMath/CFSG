module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Check

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12

open CFSG.GammaU.Native

def hjQuadFourCheck : Bool :=
  let e1 := wordR (hj_eWords.headD [])
  let e2 := wordR (hj_eWords.getD 1 [])
  let f := fixCodes e1
  isInvol e1 && isInvol e2 && commR e1 e2 && e1 != e2 && fixCodes e2 == f &&
    fixCodes (mulR e1 e2) == f

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12

end
