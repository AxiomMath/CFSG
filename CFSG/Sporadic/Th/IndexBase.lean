
module

public import CFSG.Sporadic.Th.PlaneBase
public import Certificates.Data.CFSGNative.Th.FormCheck

@[expose] public section

namespace CFSG.Sporadic.Th

open Native Pointwise

section Facts

variable (hF : OrbitFacts)
include hF

end Facts

end CFSG.Sporadic.Th
