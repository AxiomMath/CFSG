module

public import Certificates.Data.Kernel.L34Scan

public section

namespace CFSG.KC.L34Pre

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.KLie.CT (notB)

@[expose] noncomputable def mvFix (w nf : Nat) (F : Nat → Nat) (t a : Nat) : Bool :=
  strictB (pg w (mask w) t a) fun c =>
    notB (allN nf fun i => Nat.beq (pg w (mask w) (F i) c) c)

end CFSG.KC.L34Pre

end
