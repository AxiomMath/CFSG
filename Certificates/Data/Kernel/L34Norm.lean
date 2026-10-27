module

public import Certificates.Data.Kernel.L34K

public section

namespace CFSG.KC.L34Norm

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KLie.CT (andB orB notB anyN)

@[expose] noncomputable def conjPt (n w x a e : Nat) : Bool :=
  allN n fun p => Nat.beq (pg w (mask w) x (pg w (mask w) a p)) (pg w (mask w) e (pg w (mask w) x p))

@[expose] noncomputable def inPts (n w N : Nat) (P : Nat → Nat) (x a : Nat) : Bool :=
  anyN N fun j => conjPt n w x a (P j)

@[expose] noncomputable def pairPt (w u v x : Nat) : Bool :=
  andB (orB (Nat.beq (pg w (mask w) x u) u) (Nat.beq (pg w (mask w) x u) v))
    (orB (Nat.beq (pg w (mask w) x v) u) (Nat.beq (pg w (mask w) x v) v))

@[expose] noncomputable def o3Pt (n w e x : Nat) : Bool :=
  andB (notB (Nat.beq x e))
    (allN n fun p => Nat.beq (pg w (mask w) x (pg w (mask w) x (pg w (mask w) x p))) p)

@[expose] noncomputable def nfixK (n w x : Nat) : Nat :=
  CFSG.KC.HeAutK.cntR (fun p => Nat.beq (pg w (mask w) x p) p) (nat_lit 0) n

@[expose] noncomputable def bv (b : Bool) : Nat := Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) b

@[expose] noncomputable def o3Cat (n w e x : Nat) : Nat :=
  nIf(o3Pt n w e x, (strictN (nfixK n w x) fun f =>
    nIf(Nat.beq f (nat_lit 0), nat_lit 1, nIf(Nat.beq f (nat_lit 6), nat_lit 2,
      nIf(Nat.beq f (nat_lit 12), nat_lit 3, nat_lit 4)))), nat_lit 0)

@[expose] noncomputable def normCode (n w AN : Nat) (AP : Nat → Nat) (a b z u v e x : Nat) : Nat :=
  Nat.add (Nat.add (bv (andB (inPts n w AN AP x a) (inPts n w AN AP x b)))
      (Nat.mul (nat_lit 2) (bv (commPt n w x z))))
    (Nat.add (Nat.mul (nat_lit 4) (bv (pairPt w u v x))) (Nat.mul (nat_lit 8) (o3Cat n w e x)))

@[expose] noncomputable def curRun (f J : Nat → Nat) (len : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool) (fun _ c e => Nat.beq c e)
    (fun _ ih lo c e => strictB (f lo) fun v => bIf(Nat.beq v (nat_lit 0), ih (Nat.succ lo) c e,
      andB (andB (Nat.blt v (nat_lit 32))
        (Nat.beq (J c) (Nat.add (Nat.mul (nat_lit 32) lo) v))) (ih (Nat.succ lo) (Nat.succ c) e)))
    len

@[expose] noncomputable def curSl (f J : Nat → Nat) (L : Nat) (C : Nat → Nat) (s : Nat) : Bool :=
  curRun f J L (Nat.mul L s) (C s) (C (Nat.succ s))

end CFSG.KC.L34Norm

end
