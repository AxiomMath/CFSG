module

public import Certificates.Data.Kernel.BfsPin
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.ListBridge

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw

@[expose] noncomputable def rootWitK (n w R c g : Nat) : Bool :=
  strictB (pcomp n w (mask w) c (pcomp n w (mask w) (pcomp n w (mask w) g c)
    (pinvS n w (mask w) g))) fun x =>
    bAnd(Nat.beq (pcomp n w (mask w) x x) (pidn n w),
      bIf(Nat.beq x (pidn n w), false, bIf(Nat.beq x R, false, true)))

@[expose] noncomputable def rootsK (n w R N : Nat) (T WI : Nat → Nat) : Bool :=
  strictB R fun R => bAnd(canonK n w (mask w) (n * w) R,
    allN N fun i => strictB (T i) fun c =>
      bIf(Nat.beq (pcomp n w (mask w) c c) R,
        strictB (WI i) fun j => bAnd(Nat.blt j N, rootWitK n w R c (T j)), true))

end CFSG.KC.ListBridge

end
