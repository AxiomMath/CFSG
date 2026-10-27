module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGE
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGG
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGJ
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGL

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

theorem facts12_of (hG2 : FactCartanPointG2) (hT : FactList2Table)
    (hG2a : FactG2AdjointOrder) (h3D4 : Fact3D4Order) : Facts12 :=
  ⟨factCartanPointSL3_holds, factCartanPointSp4_holds, hG2, hT, factList2PSL3_of hG2a h3D4⟩

theorem facts12b_of (hL3 : FactList3Table) (hO : FactOuterLevi) (hF : FactFieldAutPointG2)
    (hJ1 : FactJ1) : Facts12b :=
  ⟨hL3, factCentL2p_holds, hO, factFieldAutPointSL3_holds, factFieldAutPointSp4_holds, hF, hJ1,
    factSL34Center_holds⟩

theorem facts12c_of (hM : FactModules3n) (hA7 : FactA7SectionCent) (hL : FactCartanLineG2) :
    Facts12c :=
  ⟨hM, factA7Cent_of hA7, factCartanLineSL3_holds, factCartanLineSp4_holds, hL,
    factNoOverlap_holds⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
