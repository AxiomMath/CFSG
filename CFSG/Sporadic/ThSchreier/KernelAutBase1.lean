
module


public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Sporadic.Th.KernelInputs
public import Certificates.Kernel.ThCent.Data

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.ComponentClassification.OuterAutomorphisms Pointwise

variable (h : Kernel.KernelFacts)
include h

end CFSG.Sporadic.ThSchreier
