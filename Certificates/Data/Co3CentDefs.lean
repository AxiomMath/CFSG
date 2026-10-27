module

public import Certificates.Data.Co3Cent

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Monster.B.Co2 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T
  CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump

@[expose] noncomputable def XB : Equiv.Perm (Fin 276) := permOfArr 276 (dElts ())[kB]!

@[expose] noncomputable def XA : Equiv.Perm (Fin 276) := permOfArr 276 (dElts ())[kA]!

end CFSG.HardMathSupport.Dickson.I271

end
