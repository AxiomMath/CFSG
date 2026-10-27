module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.Quasithin.Background.A3Structure312Facts

public section

namespace CFSG.Quasithin.Vol2.Ch11

open CFSG.Quasithin

theorem a312ListFacts_of_cat (h : QuasithinUnique.Vol2Native.A312ListFactsCat) :
    A312ListFacts := fun X _ _ hq hX ho2 T hT B hB hne =>
  h X hq ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mpr hX.1, hX.2⟩ ho2 T hT B hB hne

theorem a312Facts_of_cat (hList : QuasithinUnique.Vol2Native.A312ListFactsCat)
    (hSL2 : A312SL2Fact) : A312Facts :=
  ⟨a312ListFacts_of_cat hList, hSL2⟩

end CFSG.Quasithin.Vol2.Ch11
