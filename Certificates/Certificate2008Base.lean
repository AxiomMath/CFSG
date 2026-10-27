
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfA8Inputs
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Data
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfChecks2

@[expose] public section

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall
open CFSG.ComponentClassification.CatFactsSmall.A8 CFSG.GH74.KGroups CFSG.Certificates
open CFSG.Sporadic.Schreier Subgroup CFSG.ComponentClassification.GSThmB

local notation "PX" => Equiv.Perm (Fin 8)

