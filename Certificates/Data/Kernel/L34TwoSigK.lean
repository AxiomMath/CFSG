module

public import Certificates.Data.Kernel.L34Scan

public section

namespace CFSG.KC.L34Two

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Scan
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def conjK (n w : Nat) (BT BTI : Nat → Nat) (nb d x : Nat) : Nat :=
  strictN (Nat.mod (Nat.sub d (nat_lit 1)) nb) fun j =>
    pcomp n w (mask w) (pcomp n w (mask w) (BT j) x) (BTI j)

@[expose] noncomputable def wordK (n w : Nat) (BT BTI : Nat → Nat) (nb x : Nat) (f : Nat) :
    Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => pidn n w)
    (fun _ ih wd => strictN (Nat.land wd (nat_lit 15)) fun d =>
      nIf(Nat.beq d (nat_lit 0), pidn n w,
        pcomp n w (mask w) (conjK n w BT BTI nb d x) (ih (Nat.shiftRight wd (nat_lit 4))))) f

@[expose] noncomputable def cycL (w x p f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih q c => nIf(Nat.beq q p, c, ih (pg w (mask w) x q) (Nat.succ c))) f

@[expose] noncomputable def badP (n w x p : Nat) : Bool :=
  strictB (cycL w x p n (pg w (mask w) x p) (nat_lit 1)) fun l =>
    andB (Nat.blt (nat_lit 0) l) (notB (Nat.beq (Nat.mod (nat_lit 256) l) (nat_lit 0)))

@[expose] noncomputable def cycNP (n w x k : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun _ ih p => orB (badP n w x p) (ih (Nat.succ p))) k

@[expose] noncomputable def sigK (n w B1 B2 : Nat) (BT BTI : Nat → Nat) (nb e x wd : Nat) : Bool :=
  orB (cycNP n w x (nat_lit 7) (nat_lit 0))
    (orB (andB (commPt n w x B1) (commPt n w x B2))
      (strictB (wordK n w BT BTI nb x (nat_lit 8) wd) fun v =>
        orB (cycNP n w v (nat_lit 3) (nat_lit 0)) (notB (Nat.beq (pow2K n w (nat_lit 8) v) e))))

@[expose] noncomputable def sigSl (n w B1 B2 : Nat) (BT BTI : Nat → Nat) (nb : Nat)
    (T W : Nat → Nat) (L s : Nat) : Bool :=
  strictB (pidn n w) fun e => allN L fun i => strictB (Nat.add (Nat.mul L s) i) fun k =>
    strictB (T k) fun x => strictB (W k) fun wd => sigK n w B1 B2 BT BTI nb e x wd

end CFSG.KC.L34Two

end
