module

public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.Assembly
public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.Centralizer
public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.Five
public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.TwoElt
public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.CardPCore
public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.Outer
public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.NormR
public import CFSG.Quasithin.Vol2.KGFact12617LiePf
public import CFSG.Quasithin.Vol2.KGFact12617a
public import CFSG.Quasithin.Vol2.KGFact12617d

public section

namespace CFSG.Quasithin.H13.KG12617L52

theorem factKv12617L52_holds : FactKv12617L52 :=
  factKv12617L52_of_leaves leafCentralizer_holds leafFive_holds leafTwoElt_holds
    (leafCardPCore_of leafFive_holds leafTwoElt_holds) leafOuter_holds
    (leafNormR_of leafFive_holds leafTwoElt_holds (leafCardPCore_of leafFive_holds leafTwoElt_holds))

end CFSG.Quasithin.H13.KG12617L52
