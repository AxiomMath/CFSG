module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec93OmNS
public import CFSG.RankThree.GF2n.Stroth80.Sec93OmegaSplit
import CFSG.RankThree.GF2n.Stroth80.Sec93OmPfFinal

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank


theorem step93OmegaCaseBNSStatement_holds : Step93OmegaCaseBNSStatement := by
  intro G _ _ M Q Z B hc n t r Z0 h cfg x hxK hxQ hSL hR hLN
  exact step93OmegaCaseB_plusFour stroth34Statement_unconditional
    stroth311aStatement_unconditional stroth311bCommStatement_unconditional
    stroth311bCardStatement_unconditional stroth312bStatement_unconditional
    G M Q Z B hc n t r Z0 h cfg x hxK hxQ (S93O.omegaPlusFourNat_of_cfg cfg hxK hxQ hSL) hR hLN

end CFSG.RankThree.GF2n.Stroth80
