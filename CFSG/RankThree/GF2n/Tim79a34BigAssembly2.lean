module

public import CFSG.RankThree.GF2n.Tim79a34BigAssembly
public import CFSG.RankThree.GF2n.Tim79a34BigRoot
public import CFSG.RankThree.GF2n.Tim79aSec34Centre
public import CFSG.RankThree.GF2n.Tim79a34BigRegular
public import CFSG.RankThree.GF2n.Tim79a34BigStabQuot
public import CFSG.RankThree.GF2n.Tim79a34BigRbarIso
public import CFSG.RankThree.GF2n.Tim79a34BigB
public import CFSG.RankThree.GF2n.Tim79a34BigAlpha

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint

theorem sec34TorusStatement_of_centre (hZ : Sec34CentreTrivialStatement) :
    Sec34TorusStatement :=
  sec34TorusStatement_of_parts hZ

theorem bigRegularStatement_of_natural_holds (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) (hIW : BigIWStatement) : BigRegularStatement :=
  bigRegularStatement_of_natural hZ (sec34TorusStatement_of_centre hZ) hN hIW
    bigPLocalStatement_holds

theorem bigRbarIsoStatement_of_natural (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) (hIW : BigIWStatement) : BigRbarIsoStatement :=
  bigRbarIsoStatement_of_local hZ hN hIW bigPLocalStatement_holds
    (bigRootElement_holds bigPLocalStatement_holds)

theorem bigAlphaStatement_of_natural (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) (hIW : BigIWStatement) : BigAlphaStatement :=
  bigAlphaStatement_of_local hZ hN hIW (bigBStatement_of_local hZ hN hIW)

end CFSG.RankThree.GF2n.Tim79a
