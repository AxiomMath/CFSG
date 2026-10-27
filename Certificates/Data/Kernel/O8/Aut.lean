module

public import Certificates.Data.Kernel.O8.Nat8
public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.KC.Enum (pidn pcomp permOK pg strictB)

@[expose] noncomputable def foldQT (n w : Nat) (QT : Nat → Nat) (y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn n w)
    (fun j ih => strictN ih fun acc => nIf(Nat.beq (bitN y j) (nat_lit 1), pcomp n w (mask w) acc (QT j), acc))
    (nat_lit 6)

@[expose] noncomputable def psiTab (n w : Nat) (QT : Nat → Nat) : Nat :=
  orN (nat_lit 64) fun y => Nat.shiftLeft (foldQT n w QT y) (Nat.mul (Nat.mul n w) y)

@[expose] noncomputable def psiAt (n w T y : Nat) : Nat := fget T y (Nat.mul n w)

@[expose] noncomputable def qtCommOK (n w : Nat) (QT : Nat → Nat) : Bool :=
  andB (allN (nat_lit 6) fun i => sqIdK n w (mask w) (Nat.mul n w) (pidn n w) (QT i))
    (allN (nat_lit 6) fun i => allN (nat_lit 6) fun j => commK n w (mask w) (Nat.mul n w) (QT i) (QT j))

@[expose] noncomputable def psiRowOK (n w : Nat) (LR TRI : Nat → Nat) (BP nb : Nat) (extra : Nat → Nat → Bool)
    (T y : Nat) : Bool :=
  strictB (psiAt n w T y) fun P =>
    andB (permOK n w (mask w) (Nat.mul n w) P P)
      (andB (siftK n w (mask w) (Nat.mul n w) (pidn n w) LR TRI BP nb (nat_lit 0) P) (extra y P))

@[expose] noncomputable def baseRegOK (n w T BP nb : Nat) : Bool :=
  allN nb fun t => strictB (pg w (mask w) BP t) fun b =>
    allN (nat_lit 63) fun y => notB (Nat.beq (pg w (mask w) (psiAt n w T (Nat.succ y)) b) b)

@[expose] noncomputable def psiOrbitOK (n w T : Nat) : Bool :=
  strictB (orN (nat_lit 64) fun y => pw2 (pg w (mask w) (psiAt n w T y) (nat_lit 0))) fun O =>
    allN n fun z => orB (bit O z)
      (anyN (nat_lit 63) fun y => Nat.beq (pg w (mask w) (psiAt n w T (Nat.succ y)) z) z)

@[expose] noncomputable def autPsiOK (n w : Nat) (QT LR TRI : Nat → Nat) (BP nb : Nat)
    (extra : Nat → Nat → Bool) : Bool :=
  andB (qtCommOK n w QT) (strictB (psiTab n w QT) fun T =>
    andB (allN (nat_lit 64) (psiRowOK n w LR TRI BP nb extra T))
      (andB (baseRegOK n w T BP nb) (psiOrbitOK n w T)))

end CFSG.KC.O8

end
