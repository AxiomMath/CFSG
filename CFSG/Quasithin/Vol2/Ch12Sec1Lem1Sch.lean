module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1He
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporSchreier
public import CFSG.Sporadic.Schreier.J4SCatalog

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique

theorem lem1211HeSchreier_of
    (hS : Vol2Native.SchreierFactListCat) : Lem1211HeSchreier := by
  intro G _ _ hs hnab hqtke H K hH hK
  have : IsSimpleGroup G := hs
  exact hS ↥K (BenderBranch.isQuasisimple_of_isComponentIn hK)
    (Ch1.sqtkSimpleList_component (qtkeCore_of_cat hnab hqtke).1 hH hK)

theorem lem1211HeSchreier_holds :
    Lem1211HeSchreier :=
  lem1211HeSchreier_of (Vol2Native.schreierFactListCat_of_J4 fun _ _ _ _ _ he =>
    CFSG.Sporadic.J4Schreier.R3E_J4_catalog_Schreier he)

end CFSG.Quasithin.H13
