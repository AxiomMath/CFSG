module

public import Certificates.Data.Kernel.ListBridgeComm

public section

namespace CFSG.KC.ListBridge

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw

@[expose] noncomputable def commSelfK (n w NK : Nat) (TK : Nat → Nat) (NU : Nat) (TU W : Nat → Nat) :
    Bool :=
  allN NK fun i => strictB (TK i) fun t =>
    bIf(Nat.beq (pcomp n w (mask w) t (pcomp n w (mask w) t t)) (pidn n w),
      bIf(Nat.beq t (pidn n w), true,
        allN 9 fun k => bAnd(Nat.blt (W (Nat.add (Nat.mul 9 i) k)) NU,
          allN k fun k' => bIf(Nat.beq (pcommutK n w (TU (W (Nat.add (Nat.mul 9 i) k))) t)
            (pcommutK n w (TU (W (Nat.add (Nat.mul 9 i) k'))) t), false, true))),
      true)

end CFSG.KC.ListBridge

end
