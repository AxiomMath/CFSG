module

public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.RankThree.PartOne.SPOR.Final

public section

namespace CFSG.RankThree.PartOne.TCB

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem schreierFor_inCatalog_holds
    : SchreierFor CFSG.Assembly.InCatalog :=
  schreierFor_inCatalog_of_catalog tauCetiCatalogBridge SPOR.schreierFor_catalog

end CFSG.RankThree.PartOne.TCB
