module

public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.D4K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K

@[expose] noncomputable def siftOK (n w : Nat) (LR TRI : Nat → Nat) (BP nb G : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight G (n * w)) 0, bAnd(allN n (fun i => Nat.blt (pg w (mask w) G i) n),
    siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 G))

@[expose] noncomputable def lineAt (n w p r : Nat) (T LX : Nat → Nat) (k : Nat) : Bool :=
  !(Nat.beq (pw n w (T k) p) (pidn n w)) || Nat.beq (T k) (pidn n w) ||
    CFSG.KC.LQT.P.anyN r fun j => CFSG.KC.LQT.P.anyN p fun e => Nat.beq (T k) (pw n w (LX j) e)

end CFSG.KC.D4K

end
