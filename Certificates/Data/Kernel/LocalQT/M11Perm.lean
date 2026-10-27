module

public import Certificates.Data.Kernel.LocalQT.M11

public section

namespace CFSG.KC.LQT.M

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S

@[expose] noncomputable def p4135 (LI LF WI : List Nat) : Bool :=
  andB (allL LI (permK 11)) (andB (allL LF (permK 11)) (allL WI fun w => permK 11 (sndM w)))

@[expose] noncomputable def p4054 (RO : List Nat) (T0 : Nat) (S0 C0 : List Nat) : Bool :=
  andB (permK 11 T0) (andB (allL RO (permK 11)) (andB (allL S0 (permK 11)) (allL C0 (permK 11))))

end CFSG.KC.LQT.M

end
