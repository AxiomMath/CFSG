module

public import Certificates.Data.Kernel.L34K

public section

namespace CFSG.KC.L34Key

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def sqPt (n w x r : Nat) : Bool :=
  allN n fun p => Nat.beq (pg w (mask w) x (pg w (mask w) x p)) (pg w (mask w) r p)

@[expose] noncomputable def keyK (n w m : Nat) (C : Nat → Nat) (r x : Nat) : Bool :=
  orB (notB (sqPt n w x r)) (notB (allN m fun j => strictB (C j) fun v =>
    notB (andB (notB (commPt n w x v)) (notB (Nat.beq (pcomp n w (mask w) x v)
      (pcomp n w (mask w) (pcomp n w (mask w) r v) x))))))

@[expose] noncomputable def cqK (n w m : Nat) (C CI : Nat → Nat) (r : Nat) : Bool :=
  strictB (pidn n w) fun e => allN m fun a => strictB (C a) fun x =>
    orB (notB (Nat.beq (pcomp n w (mask w) x x) r)) (notB (allN m fun b =>
      strictB (pcomp n w (mask w) x (pcomp n w (mask w) (pcomp n w (mask w) (C b) x) (CI b)))
        fun q => notB (andB (invPt n w q) (andB (notB (Nat.beq q e)) (notB (Nat.beq q r))))))

end CFSG.KC.L34Key

end
