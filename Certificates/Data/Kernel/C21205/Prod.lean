module

public import Certificates.Data.Kernel.C21205.Sylow

public section

namespace CFSG.KC.C21205

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.G24
open CFSG.LargeExtraspecial.AS35QCo.Native (idc repc witc)

@[expose] noncomputable def bigOrderK (x : Nat) : Bool :=
  andB (notB (Nat.beq x idc)) <| andB (notB (Nat.beq (mulK x x) idc)) <|
    andB (notB (Nat.beq (mulK (mulK x x) x) idc)) (notB (Nat.beq (mulK (mulK x x) (mulK x x)) idc))

@[expose] noncomputable def prodK (k : Nat) : Bool :=
  andB (isSpK witc.1) <| andB (Nat.beq (mulK witc.1 witc.2) idc) <|
    andB (Nat.beq (mulK witc.2 witc.1) idc)
      (bigOrderK (mulK (repc k) (mulK (mulK witc.1 (repc k)) witc.2)))

end CFSG.KC.C21205

end
