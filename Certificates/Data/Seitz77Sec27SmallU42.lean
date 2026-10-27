module

public import CFSG.GH74.KGroups.NativeChecks2
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public meta import CFSG.GH74.KGroups.NativeChecks2
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData

public section

namespace Certificates.Seitz77Sec27

open CFSG.KGroups.Native CFSG.GH74.KGroups.NativeChecks
  CFSG.ComponentClassification.CatFactsSmall.PSp43

@[expose] def u42CensusCheckL (LA LP : List (Array Nat)) : Bool :=
  LP.all (fun s => !isInvolA 45 s || !decide (5 ∣ centLenA 45 LA s)) &&
    LA.all (fun s => !isInvolA 45 s || !decide (5 ∣ centLenA 45 LA s) ||
      decide (2 ^ 5 ∣ centLenA 45 LA s))

@[expose] def u42CensusCheck : Bool := u42CensusCheckL (enumA QA45) (enumA QP45)

end Certificates.Seitz77Sec27
