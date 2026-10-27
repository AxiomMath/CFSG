module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverTop
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTitsProof
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.TitsCoverMain

public section

namespace CFSG.Quasithin

theorem lemma115_3_List_native
    : CFSG.QuasithinUnique.Lemma115_3_List :=
  CFSG.QuasithinUnique.lemma115_3_List_of_rest_inputs'
    CFSG.QuasithinUnique.K1.titsSylowCentralizingAutInner
    (CFSG.QuasithinUnique.Ch1.sporadicRestAutInner_of_J4OutOdd
      CFSG.QuasithinUnique.Setup.X1.j4OuterOdd)
    CFSG.QuasithinUnique.Ch1.titsTwoCoverTrivial

end CFSG.Quasithin
