module

public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoFinal
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoExceptional

public section

namespace CFSG.RankThree.PartOne

theorem catalogPrimeTwoAutomorphismsInner_of_orthogonal_sporadic_simple
    (horth : OrthogonalOuterPrimeTwoTrivial) (hsp : ∀ s, SporadicOuterSmallSimple s) :
    CatalogPrimeTwoAutomorphismsInner :=
  catalogPrimeTwoAutomorphismsInner_of_open_inspections_simple horth
    exceptionalOuterPrimeTwoTrivial hsp

end CFSG.RankThree.PartOne
