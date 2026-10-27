module

public import CFSG.Adapters.TauCetiExceptional.EvenB1
public import CFSG.Adapters.TauCetiExceptional.ReeCatalog
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
public import CFSG.RankThree.PartOne.TCB.Sporadic
public import CFSG.RankThree.PartOne.TCB.Schreier
public import CFSG.Adapters.TauCetiExceptional.B1Sporadic

public section

namespace CFSG.RankThree.PartOne.TCB

open TauCeti CFSG.QuasithinUnique.B1 CFSG.TauCetiBridge.Even
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem catalogBridgeFor_all (i : CFSGIndex) : CatalogBridgeFor i :=
  catalogBridgeFor_of_nonEven ({ orthogonalOdd := CFSG.RankThree.PartTwo.Census.catalogBridgeFor_B,
                                 orthogonalPlus := CFSG.RankThree.PartTwo.Census.catalogBridgeFor_D,
                                 orthogonalMinus := CFSG.RankThree.PartTwo.Census.catalogBridgeFor_twistedD,
                                 reeG2 := CFSG.TauCetiBridge.catalogBridgeFor_reeG2,
                                 reeF4 := CFSG.TauCetiBridge.catalogBridgeFor_reeF4,
                                 tits := CFSG.TauCetiBridge.catalogBridgeFor_tits,
                                 sporadic := (CFSG.TauCetiBridge.catalogBridgeFor_sporadic_of_forall
                                     nonempty_carrier_mulEquiv_group) }) i

theorem tauCetiCatalogBridge : TauCetiCatalogBridge :=
  fun S _ _ _ _ hS => catalog_of_inCatalog catalogBridgeFor_all S hS

theorem tcKGroupBridge : CFSG.QuasithinUnique.TCKGroupBridge :=
  tcKGroupBridge_of_bridges catalogBridgeFor_all

theorem schreierFor_inCatalog (hS : SchreierFor CFSG.Blueprint.Catalog) :
    SchreierFor CFSG.Assembly.InCatalog :=
  schreierFor_inCatalog_of_catalog tauCetiCatalogBridge hS

end CFSG.RankThree.PartOne.TCB
