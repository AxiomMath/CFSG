module

public import Certificates.Data.Kernel.L34K

public section

namespace CFSG.KC.ChengHeld

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def commP (n w x y : Nat) : Bool :=
  Nat.beq (pcomp n w (mask w) x y) (pcomp n w (mask w) y x)

@[expose] noncomputable def centSqK (n w cnt : Nat) (T : Nat → Nat) (cs zs : List Nat) : Bool :=
  allN cnt fun i => strictB (T i) fun x =>
    orB (notB (cs.all (commP n w x))) (zs.any (Nat.beq (pcomp n w (mask w) x x)))

end CFSG.KC.ChengHeld

end
