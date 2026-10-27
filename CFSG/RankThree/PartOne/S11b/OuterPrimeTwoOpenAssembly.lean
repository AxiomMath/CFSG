module

public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoAssembly
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicOpen

public section

namespace CFSG.RankThree.PartOne

theorem catalogPrimeTwoAutomorphismsInner_of_orthogonal_simple
    (horth : OrthogonalOuterPrimeTwoTrivial) (hopen : SporadicOuterOrderLeTwoSimple) :
    CatalogPrimeTwoAutomorphismsInner :=
  catalogPrimeTwoAutomorphismsInner_of_orthogonal_sporadic_simple horth
    (sporadicOuterSmallSimple_of_simple hopen)

end CFSG.RankThree.PartOne
