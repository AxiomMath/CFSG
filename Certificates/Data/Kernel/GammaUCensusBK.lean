module

public import Certificates.Data.Kernel.GammaUCensusK
public import Certificates.Data.Kernel.IdxFourLbarK

public section

namespace CFSG.KC.GUC

open CFSG.KC.IF4C CFSG.KC.IF4L

@[expose] noncomputable def cgOK (CG : Nat) : Bool :=
  allBelow 32 fun c => commOK (five CG c) && subOK (five CG c)

end CFSG.KC.GUC

end
