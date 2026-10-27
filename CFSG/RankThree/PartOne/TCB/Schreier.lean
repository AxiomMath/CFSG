module

public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement

public section

namespace CFSG.RankThree.PartOne.TCB

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem schreierFor_inCatalog_of_catalog (hbridge : TauCetiCatalogBridge)
    (hS : SchreierFor CFSG.Blueprint.Catalog) : SchreierFor CFSG.Assembly.InCatalog :=
  fun X _ _ _ hnonab hX => hS X hnonab (hbridge X hnonab hX)

end CFSG.RankThree.PartOne.TCB
