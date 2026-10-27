module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.TwoM22

open CFSG.KC.Enum

@[expose] noncomputable def wordId (n w m a b ai bi W len : Nat) : Bool :=
  allN n (fun p => Nat.beq (wpt w m a b ai bi W len p) p)

@[expose] noncomputable def relOK (n w m a b ai bi : Nat) (ws : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun d _ ih => bAnd(wordId n w m a b ai bi d.1 d.2, ih)) ws

@[expose] noncomputable def conjOK (n w m a b ai bi t x W len : Nat) : Bool :=
  allN n (fun p => Nat.beq (pg w m t (pg w m x (pg w m t p))) (wpt w m a b ai bi W len p))

@[expose] noncomputable def wordEqOK (n w m a b ai bi g W len : Nat) : Bool :=
  allN n (fun p => Nat.beq (pg w m g p) (wpt w m a b ai bi W len p))

@[expose] noncomputable def wordMulOK (n w m a b ai bi g W len s : Nat) : Bool :=
  allN n (fun p => Nat.beq (pg w m g p) (wpt w m a b ai bi W len (pg w m s p)))

@[expose] noncomputable def trPar (tr p : Nat) : Nat :=
  fld(tr, Nat.mul (nat_lit 16) p, nat_lit 1023)

@[expose] noncomputable def trLab (tr p : Nat) : Nat :=
  fld(tr, Nat.add (Nat.mul (nat_lit 16) p) (nat_lit 10), nat_lit 1)

@[expose] noncomputable def trDep (tr p : Nat) : Nat :=
  fld(tr, Nat.add (Nat.mul (nat_lit 16) p) (nat_lit 11), nat_lit 31)

@[expose] noncomputable def treeOK (n w m a b tr : Nat) : Bool :=
  allN n (fun p => bIf(Nat.beq p (nat_lit 0), Nat.beq (trDep tr p) (nat_lit 0),
    strictB (trPar tr p) (fun par => bAnd(Nat.blt par n,
      bAnd(Nat.beq (Nat.succ (trDep tr par)) (trDep tr p),
        Nat.beq (pg w m (nIf(Nat.beq (trLab tr p) (nat_lit 0), a, b)) par) p)))))

@[expose] noncomputable def fix2OK (n w m a b ai bi W len x0 x1 : Nat) : Bool :=
  allN n (fun p => bIf(Nat.beq (wpt w m a b ai bi W len p) p,
    bIf(Nat.beq p x0, true, Nat.beq p x1),
    bIf(Nat.beq p x0, false, bIf(Nat.beq p x1, false, true))))

@[expose] noncomputable def allFix (w m a b ai bi : Nat) (ks : List (Nat × Nat)) (p : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun d _ ih => bAnd(Nat.beq (wpt w m a b ai bi d.1 d.2 p) p, ih)) ks

@[expose] noncomputable def fix1OK (n w m a b ai bi : Nat) (ks : List (Nat × Nat)) (x0 : Nat) :
    Bool :=
  allN n (fun p => bIf(allFix w m a b ai bi ks p, Nat.beq p x0, bIf(Nat.beq p x0, false, true)))

@[expose] noncomputable def pm660 : Nat :=
  Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 6600)) (nat_lit 1)

@[expose] noncomputable def pm22 : Nat :=
  Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 110)) (nat_lit 1)

@[expose] noncomputable def rE (F : Nat → Nat) (k : Nat) : Nat := Nat.land (F k) pm660

@[expose] noncomputable def rE22 (F : Nat → Nat) (k : Nat) : Nat := fld(F k, nat_lit 6600, pm22)

@[expose] noncomputable def rR (F : Nat → Nat) (k g : Nat) : Nat :=
  fld(F k, Nat.add (nat_lit 6710) (Nat.mul (nat_lit 9) g), nat_lit 511)

@[expose] noncomputable def rPar (F : Nat → Nat) (k : Nat) : Nat :=
  fld(F k, nat_lit 6755, nat_lit 511)

@[expose] noncomputable def rLab (F : Nat → Nat) (k : Nat) : Nat :=
  fld(F k, nat_lit 6764, nat_lit 7)

@[expose] noncomputable def rDep (F : Nat → Nat) (k : Nat) : Nat :=
  fld(F k, nat_lit 6767, nat_lit 255)

@[expose] noncomputable def rOdd (F : Nat → Nat) (k : Nat) : Nat :=
  fld(F k, nat_lit 6775, nat_lit 1)

@[expose] noncomputable def rPt (F : Nat → Nat) (k : Nat) : Nat :=
  fld(F k, nat_lit 6776, nat_lit 1023)

@[expose] noncomputable def closOK (F : Nat → Nat) (G G22 : List Nat) (k e e22 : Nat) (g : Nat) :
    Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(
    strictB (rR F k j) (fun R => bAnd(Nat.blt R (nat_lit 512),
      bAnd(Nat.beq (pcomp (nat_lit 660) (nat_lit 10) (nat_lit 1023) e (G.getD j (nat_lit 0)))
          (rE F R),
        Nat.beq (pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) e22 (G22.getD j (nat_lit 0)))
          (rE22 F R)))),
    ih)) g

@[expose] noncomputable def recOK (F : Nat → Nat) (G G22 : List Nat) (a b ai bi zW zL k : Nat) :
    Bool :=
  strictB (rE F k) (fun e => strictB (rE22 F k) (fun e22 =>
  strictB (rPar F k) (fun par => strictB (rLab F k) (fun lab =>
  strictB (rDep F k) (fun dep => strictB (rOdd F k) (fun odd =>
  bAnd(bIf(Nat.beq k (nat_lit 0), true, Nat.blt (rE F (Nat.sub k (nat_lit 1))) e),
  bAnd(closOK F G G22 k e e22 (nat_lit 5),
  bAnd(bIf(Nat.beq dep (nat_lit 0),
      bAnd(Nat.beq e (pidn (nat_lit 660) (nat_lit 10)),
        bAnd(Nat.beq e22 (pidn (nat_lit 22) (nat_lit 5)), Nat.beq odd (nat_lit 0))),
      bAnd(Nat.blt par (nat_lit 512), bAnd(Nat.blt lab (nat_lit 5),
        bAnd(Nat.beq (Nat.succ (rDep F par)) dep, bAnd(Nat.beq (rR F par lab) k,
          Nat.beq odd
            (Nat.xor (rOdd F par) (nIf(Nat.beq lab (nat_lit 4), nat_lit 1, nat_lit 0)))))))),
  bIf(Nat.beq odd (nat_lit 0), true, strictB (rPt F k) (fun x =>
    bAnd(Nat.blt x (nat_lit 660),
    bIf(Nat.beq (pg (nat_lit 10) (nat_lit 1023) e (pg (nat_lit 10) (nat_lit 1023) e x))
        (wpt (nat_lit 10) (nat_lit 1023) a b ai bi zW zL x), false, true)))))))))))))

@[expose] noncomputable def recRange (F : Nat → Nat) (G G22 : List Nat)
    (a b ai bi zW zL lo cnt : Nat) : Bool :=
  allN cnt (fun j => recOK F G G22 a b ai bi zW zL (Nat.add lo j))

end CFSG.KC.TwoM22

end
