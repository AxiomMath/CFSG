module

public import Certificates.Data.Kernel.LocalQT.Lat

public section

namespace CFSG.KC.M23Asl

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.L

@[expose] noncomputable def yK (n : Nat) (G : List Nat) (N : Nat) (A : List Nat) (S : SetK) :
    Bool :=
  andB (closedK n G S) (andB (Nat.beq S.size N) (allL A (memT S.t)))

@[expose] noncomputable def yxK (n : Nat) (G : List Nat) (N x : Nat) (A : List Nat) (S : SetK) :
    Bool :=
  andB (notB (memT S.t x)) (yK n G N A S)

end CFSG.KC.M23Asl

end
