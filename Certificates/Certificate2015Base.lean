
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3P45Inputs
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallArrChecks
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Gen
public meta import CFSG.GH74.KGroups.Checks3

@[expose] public section

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall
open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Certificates
open CFSG.Sporadic.Schreier Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.KGroups.Native CFSG.GH74.KGroups.NativeChecks

local notation "P45" => Equiv.Perm (Fin 45)

public section

namespace Certificates

end Certificates
