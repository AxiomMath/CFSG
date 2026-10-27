module

public import Certificates.Data.Kernel.A45Cls.Pair

public section

namespace CFSG.KC.A45Cls

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind

@[expose] noncomputable def exN (N : Nat) (f : Nat → Bool) : Bool := !allN N fun i => !f i

@[expose] noncomputable def cjAll (n w N : Nat) (X Y : Nat → Nat) (u : Nat) : Bool :=
  allN N fun j => exN N fun m => eq3 n w (mask w) (Y m) u (X j) u

@[expose] noncomputable def cjBy (n w N : Nat) (X : Nat → Nat) (u v : Nat) : Bool :=
  exN N fun k => eq22 n w (mask w) (X k) u v (X k)

@[expose] noncomputable def pockD (n w N : Nat) (X Y : Nat → Nat) (t u : Nat) : Bool :=
  !invFixK n w 5 u ||
    (cjAll n w N X X u && cjAll n w N Y Y u && cjBy n w N X u (pcomp n w (mask w) u t) &&
      cjBy n w N Y u (pcomp n w (mask w) u t)) ||
    (cjAll n w N X Y u && cjAll n w N Y X u && invFixK n w 13 (pcomp n w (mask w) u t))

@[expose] noncomputable def pockE (n w N : Nat) (X Y : Nat → Nat) (t u : Nat) : Bool :=
  !invFixK n w 7 u || invFixK n w 15 (pcomp n w (mask w) u t) ||
    exN N fun j => allN N fun m => !eq3 n w (mask w) (Y m) u (X j) u

@[expose] noncomputable def f6K (n w N : Nat) (T : Nat → Nat) (R Y : Nat) : Bool :=
  allN N fun i => strictB (T i) fun v => !isInvK n w v ||
    eq22 n w (mask w) v (pidn n w) R (pidn n w) || !eq22 n w (mask w) v Y Y v ||
    Nat.beq (fixK n w v) 13 || Nat.beq (fixK n w v) 15

end CFSG.KC.A45Cls

end
