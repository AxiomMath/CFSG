module

public import Certificates.Data.Kernel.Fi22Cls.Check

public section

namespace CFSG.KC.Fi22Reps

open CFSG.KC.Enum CFSG.KC.Fi22S0 CFSG.KC.Fi22Cls

@[expose] noncomputable def xorB (a b : Bool) : Bool := bIf(a, bIf(b, false, true), b)

@[expose] noncomputable def invL (c : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), nat_lit 0, nIf(Nat.beq c (nat_lit 1), nat_lit 2, nat_lit 1))

@[expose] noncomputable def wAp (LT : Nat → Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih W x => strictN (ih (Nat.shiftRight W (nat_lit 2)) x) fun y =>
      ent (LT (Nat.land W (nat_lit 3))) y)

@[expose] noncomputable def wInv (LT : Nat → Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih W x => strictN (ent (LT (invL (Nat.land W (nat_lit 3)))) x) fun y =>
      ih (Nat.shiftRight W (nat_lit 2)) y)

@[expose] noncomputable def dE (LT : Nat → Nat) (e p : Nat) : Nat :=
  strictN (Nat.land e (nat_lit 31)) fun m => strictN (Nat.shiftRight e (nat_lit 5)) fun W =>
    strictN (wInv LT m W p) fun y => strictN (ent (LT (nat_lit 0)) y) fun z => wAp LT m W z

@[expose] noncomputable def cmE (LT : Nat → Nat) (e w : Nat) : Bool := Nat.beq (dE LT e w) w

@[expose] noncomputable def wordC (LT wd : Nat → Nat) (v : Nat) : Bool :=
  strictB (wd v) fun e =>
    Nat.beq (wAp LT (Nat.land e (nat_lit 31)) (Nat.shiftRight e (nat_lit 5)) (nat_lit 0)) v

@[expose] noncomputable def xtC (RX gR pp pj nd : Nat → Nat) (s t : Nat) : Bool :=
  strictB (nd t) fun n => strictB (nd (Nat.sub t (nat_lit 1))) fun p => strictB (pj n) fun j =>
    bAnd(Nat.beq (pp n) p, bAnd(Nat.blt p n, bAnd(Nat.blt j (nat_lit 3),
      bIf(Nat.beq t (nat_lit 1), bAnd(Nat.beq p (nat_lit 0), Nat.beq (RX s) (gR j)),
        compOK (RX (Nat.add s (Nat.sub t (nat_lit 1)))) (gR j)
          (RX (Nat.add s (Nat.sub t (nat_lit 2))))))))

@[expose] noncomputable def ptE (e : Nat) : Nat := Nat.land e (nat_lit 4095)

@[expose] noncomputable def phiC (LT wd : Nat → Nat) (X : Nat) (P nL : Nat → Nat) (L m : Nat) :
    Bool :=
  strictB (P m) fun e => strictB (ptE e) fun p => strictB fld(e, nat_lit 12, nat_lit 3) fun tag =>
    strictB fld(e, nat_lit 16, nat_lit 4095) fun u => strictB fld(e, nat_lit 28, nat_lit 4095)
      fun w => bAnd(Nat.blt p (nat_lit 3510),
        bIf(Nat.beq tag (nat_lit 0), Nat.beq (ent X p) p,
        bIf(Nat.beq tag (nat_lit 1), bAnd(Nat.blt u L, Nat.beq (nL u) m),
        bIf(Nat.beq tag (nat_lit 2), bAnd(Nat.blt u m, bAnd(Nat.blt w m,
            Nat.beq p (dE LT (wd (ptE (P u))) (ptE (P w))))),
          bAnd(Nat.blt u m, Nat.beq p (ent X (ptE (P u))))))))

@[expose] noncomputable def levC (LT wd : Nat → Nat) (X : Nat) (P cd cl cb : Nat → Nat)
    (n s f1 f2 w : Nat) : Bool :=
  strictB (cd w) fun c => strictB (Nat.shiftRight c (nat_lit 13)) fun tag =>
    strictB (Nat.land c (nat_lit 8191)) fun v =>
      bIf(Nat.beq tag (nat_lit 0), bAnd(Nat.blt v s, Nat.beq (cl v) w),
      bIf(Nat.beq tag (nat_lit 1), bAnd(Nat.blt v n, bAnd(Nat.beq (ptE (P v)) w,
          bIf(Nat.beq w (ptE (P n)), false, true))),
      bIf(Nat.beq tag (nat_lit 2), bAnd(Nat.blt v n,
          xorB (cmE LT (wd (ptE (P v))) w) (Nat.beq (cb v) (nat_lit 1))),
      bIf(Nat.beq tag (nat_lit 3),
          xorB (cmE LT (wd w) (ent X w)) (Nat.beq f1 (nat_lit 1)),
      bIf(Nat.beq tag (nat_lit 4), bAnd(Nat.beq f2 (nat_lit 1), bAnd(Nat.blt v (nat_lit 3510),
          Nat.beq (dE LT (wd w) (ent X v)) v)), false)))))

@[expose] noncomputable def levB (LT wd : Nat → Nat) (X : Nat) (P cb : Nat → Nat) (n f1 m : Nat) :
    Bool :=
  strictB (ptE (P n)) fun b => bAnd(
    bIf(Nat.beq m (nat_lit 0),
      bIf(xorB (cmE LT (wd b) (ent X b)) (Nat.beq f1 (nat_lit 1)), false, true), true),
    bIf(Nat.blt m n,
      bIf(xorB (cmE LT (wd (ptE (P m))) b) (Nat.beq (cb m) (nat_lit 1)), false, true), true))

@[expose] noncomputable def scanC (LT wd : Nat → Nat) (X : Nat) (P : Nat → Nat) (n f2 p : Nat) :
    Bool :=
  bIf(Nat.beq f2 (nat_lit 1),
    bIf(Nat.beq (dE LT (wd (ptE (P n))) (ent X p)) p, false, true), true)

@[expose] noncomputable def fixC (X : Nat) (P fp : Nat → Nat) (nF w : Nat) : Bool :=
  bIf(Nat.beq (ent X w) w, strictB (fp w) fun m => bAnd(Nat.blt m nF, Nat.beq (ptE (P m)) w),
    true)

@[expose] noncomputable def sepC (LT wd P sw : Nat → Nat) (nF m1 : Nat) : Bool :=
  strictB (ptE (P m1)) fun i => allN nF fun m2 =>
    bIf(Nat.blt m1 m2, strictB (ptE (P m2)) fun j =>
      bIf(Nat.beq i j, true, bIf(cmE LT (wd i) j,
        strictB (sw (Nat.add (Nat.mul nF m1) m2)) fun e1 =>
          strictB (sw (Nat.add (Nat.mul nF m2) m1)) fun e2 =>
            strictB (ptE (P e1)) fun x1 => strictB (ptE (P e2)) fun x2 =>
              bAnd(Nat.blt e1 nF, bAnd(Nat.blt e2 nF,
                bAnd(cmE LT (wd x1) j, bAnd(bIf(cmE LT (wd x1) i, false, true),
                  bAnd(cmE LT (wd x2) i, bIf(cmE LT (wd x2) j, false, true)))))), true)), true)

@[expose] noncomputable def ordC (L w4 : Nat → Nat) (len X k0 : Nat) : Bool :=
  bAnd(allN len fun t => Nat.blt (w4 t) (nat_lit 32),
    strictB (wordK L w4 len (nat_lit 0) k0) fun K1 => strictB (wordK L w4 len (nat_lit 0) K1)
      fun K2 => strictB (wordK L w4 len (nat_lit 0) (wordK L w4 len (nat_lit 0) K2)) fun K4 =>
        bAnd(bIf(Nat.beq K2 k0, false, true), bAnd(Nat.beq K4 k0,
          Nat.beq (mapK X K1) (wordK L w4 len (nat_lit 0) (mapK X k0)))))

end CFSG.KC.Fi22Reps

end
