module

public import Certificates.Data.Kernel.L34W.Field23200
public import Certificates.Data.Kernel.L34W.Tab42

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def fieldP (T G : Nat → Nat) (R : Nat) : Bool :=
  CFSG.KC.Mono.allR 0 64 fun k =>
    strictB (tgK G k) fun t =>
      !(Nat.beq (pcomp 42 6 (mask 6) t R) (pcomp 42 6 (mask 6) R t)) || fourthC T k

end CFSG.KC.L34W

end
