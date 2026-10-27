module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.ThDemp

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Loop

@[expose] noncomputable def lget (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun h _ ih i => Nat.rec (motive := fun _ => Nat) h (fun j _ => ih j) i) l i

@[expose] noncomputable def lgetL (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun h _ ih i => Nat.rec (motive := fun _ => List Nat) h (fun j _ => ih j) i) l i

structure DempData where
  c : Nat
  rm : Nat
  tm0 : Nat
  tm1 : Nat
  tm2 : Nat
  tm3 : Nat
  tm4 : Nat
  tm5 : Nat
  tm6 : Nat
  tm7 : Nat
  up : Nat
  dg : Nat
  ONE : Nat
  SA : Nat
  SB : Nat
  regs : List Nat
  cs1 : List Nat
  cs2 : List Nat
  r1 : Nat
  nreg : Nat
  rd : Nat
  pr : Nat
  npr : Nat
  L : Nat
  fr : List Nat
  bv : List Nat
  osz : List Nat
  pts : List (List Nat)
  tr : List (List Nat)
  tree : List (List Nat)
  ord : List (List Nat)
  res : List (List Nat)

namespace DempData

variable (D : DempData)

@[expose] noncomputable def RB (r : Nat) : Nat := lget D.regs r

@[expose] noncomputable def S (g : Nat) : Nat := D.RB (regAt D.pr g)

@[expose] noncomputable def trR (l i : Nat) : Nat := lget (lgetL D.tr l) i

@[expose] noncomputable def T (l i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (D.RB (D.trR l i)) D.ONE (Nat.beq (D.trR l i) (nat_lit 0))

@[expose] noncomputable def P (l i : Nat) : Nat := lget (lgetL D.pts l) i

@[expose] noncomputable def frL (l : Nat) : Nat := lget D.fr l

@[expose] noncomputable def oszL (l : Nat) : Nat := lget D.osz l

@[expose] noncomputable def bvL (l : Nat) : Nat := lget D.bv l

@[expose] noncomputable def mul (A B : Nat) : Nat := mulB D.c D.rm A B

@[expose] noncomputable def stepY (k y X : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (D.mul (D.T k y) X) X (Nat.beq y (nat_lit 0))

@[expose] noncomputable def sift (l e : Nat) (X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) X
    (fun q acc => D.stepY (Nat.add (Nat.add l (nat_lit 1)) q)
      (bitsN e (Nat.mul (nat_lit 8) (Nat.succ q)) (nat_lit 8)) acc)
    (Nat.sub (Nat.sub D.L l) (nat_lit 1))

end DempData

open DempData

@[expose] noncomputable def slpChk (D : DempData) : Bool :=
  andB (constsOK D.c D.rm D.tm0 D.tm1 D.tm2 D.tm3 D.tm4 D.tm5 D.tm6 D.tm7 D.up D.dg D.ONE)
  (andB (Nat.beq (D.RB 1) D.SA) (andB (Nat.beq (D.RB 2) D.SB)
  (andB (Nat.beq (runSlp D.RB D.c D.rm D.ONE D.cs1 (nat_lit 3)) D.r1)
    (Nat.beq (runSlp D.RB D.c D.rm D.ONE D.cs2 D.r1) D.nreg))))

@[expose] noncomputable def DempData.marks (D : DempData) : Nat :=
  Nat.lor (Nat.shiftLeft (nat_lit 1) (regAt D.rd 0)) (Nat.shiftLeft (nat_lit 1) (regAt D.rd 1))

@[expose] noncomputable def markChk (D : DempData) : Bool :=
  andB (Nat.blt D.nreg (Nat.shiftLeft (nat_lit 1) (nat_lit 11)))
    (andB (regsIn D.rd (nat_lit 2) D.r1)
    (andB (regsIn D.pr D.npr D.nreg)
    (andB (Nat.ble (nat_lit 2) D.npr) (andB (Nat.ble D.npr (nat_lit 64))
    (andB (Nat.beq (regAt D.pr 0) (regAt D.rd 0)) (andB (Nat.beq (regAt D.pr 1) (regAt D.rd 1))
      (allMarked D.pr D.npr (Nat.shiftRight
        (runMarked D.cs2 (Nat.add D.r1 (Nat.mul (nat_lit 2048) D.marks))) (nat_lit 11)))))))))

@[expose] noncomputable def frChk (D : DempData) : Bool :=
  andB (Nat.beq (D.frL 0) (nat_lit 0)) (andB (Nat.beq (D.frL D.L) D.npr)
    (allBelow D.L (nat_lit 1) (fun l => Nat.ble (D.frL l) (D.frL (Nat.succ l)))))

@[expose] noncomputable def levelChk (D : DempData) (l : Nat) : Bool :=
  (fun n => andB (Nat.blt (nat_lit 0) n) (andB (Nat.blt n (nat_lit 256))
  (andB (Nat.blt (D.bvL l) (Nat.shiftLeft (nat_lit 1) (nat_lit 248)))
  (andB (Nat.beq (D.P l 0) (D.bvL l)) (andB (Nat.beq (D.trR l 0) (nat_lit 0))
  (andB (allBelow n (nat_lit 4) (fun i => Bool.rec (motive := fun _ => Bool) true
      ((fun e => (fun par g => andB (Nat.blt par i) (andB (Nat.ble (D.frL l) g) (andB (Nat.blt g D.npr)
          (andB (Nat.blt (nat_lit 0) (D.trR l i)) (andB (Nat.blt (D.trR l i) D.nreg)
          (andB (Nat.beq (D.RB (D.trR l i)) (D.mul (D.T l par) (D.S g)))
            (Nat.beq (D.P l i) (vecB D.rm (D.P l par) (D.S g)))))))))
          (Nat.land e (nat_lit 8191)) (Nat.shiftRight e (nat_lit 13)))
        (lget (lgetL D.tree l) i))
      (Nat.blt (nat_lit 0) i)))
  (andB (allBelow n (nat_lit 4) (fun i => Nat.blt (lget (lgetL D.ord l) i) n))
  (andB (allBelow (Nat.sub n (nat_lit 1)) (nat_lit 4) (fun i =>
      Nat.blt (D.P l (lget (lgetL D.ord l) i)) (D.P l (lget (lgetL D.ord l) (Nat.succ i)))))
    (allBelow D.npr (nat_lit 1) (fun g => Bool.rec (motive := fun _ => Bool) true
      (Nat.beq (vecB D.rm (D.bvL l) (D.S g)) (D.bvL l)) (Nat.ble (D.frL (Nat.succ l)) g)))))))))))
  (D.oszL l)

@[expose] noncomputable def resChk (D : DempData) (l : Nat) : Bool :=
  (fun n m => allBelow (Nat.mul n m) (Nat.add (Nat.shiftRight (Nat.mul n m) (nat_lit 6)) (nat_lit 1))
    (fun p => (fun i g e => (fun z => andB (Nat.blt z n)
        (andB (allBelow (Nat.sub (Nat.sub D.L l) (nat_lit 1)) (nat_lit 1) (fun q =>
            Nat.blt (bitsN e (Nat.mul (nat_lit 8) (Nat.succ q)) (nat_lit 8))
              (D.oszL (Nat.add (Nat.add l (nat_lit 1)) q))))
          (Nat.beq (D.mul (D.T l i) (D.S g)) (D.sift l e (D.T l z)))))
        (Nat.land e (nat_lit 255)))
      (Nat.div p m) (Nat.add (D.frL l) (Nat.mod p m)) (lget (lgetL D.res l) p)))
  (D.oszL l) (Nat.sub D.npr (D.frL l))

@[expose] noncomputable def shapeChk (D : DempData) : Bool :=
  andB (markChk D) (andB (frChk D) (andB (Nat.beq D.L (nat_lit 6))
  (andB (Nat.beq (D.oszL 0) (nat_lit 31)) (andB (Nat.beq (D.oszL 1) (nat_lit 30))
  (andB (Nat.beq (D.oszL 2) (nat_lit 28)) (andB (Nat.beq (D.oszL 3) (nat_lit 24))
  (andB (Nat.beq (D.oszL 4) (nat_lit 16)) (Nat.beq (D.oszL 5) (nat_lit 32)))))))))

@[expose] noncomputable def levelsChk (D : DempData) : Bool :=
  andB (levelChk D 0) (andB (levelChk D 1) (andB (levelChk D 2) (andB (levelChk D 3)
    (andB (levelChk D 4) (levelChk D 5)))))

@[expose] noncomputable def dempChk (D : DempData) : Bool :=
  andB (slpChk D) (andB (shapeChk D) (andB (levelsChk D)
  (andB (resChk D 0) (andB (resChk D 1) (andB (resChk D 2) (andB (resChk D 3)
    (andB (resChk D 4) (resChk D 5))))))))

end CFSG.KC.ThDemp

end
