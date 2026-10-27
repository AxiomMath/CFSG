module

public import Certificates.Data.Kernel.Fi22.Letters

public section

set_option maxRecDepth 400000

namespace CFSG.KS.Fi22Gen

open CFSG.KC.Enum CFSG.KS.Fi22L

@[expose] noncomputable def LT (l x : Nat) : Nat := LJk ljPacked slpPacked l x

@[expose] noncomputable def AB (l x : Nat) : Nat := lk (orbT l) x

@[expose] noncomputable def wAp (f : Nat → Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  List.foldr (fun l y => f l y) x w

@[expose] noncomputable def lettersLt (m : Nat) (w : List Nat) : Bool :=
  List.all w fun l => Nat.blt l m

@[expose] noncomputable def gD (L : List Nat) (i : Nat) : Nat := List.getD L i (nat_lit 0)

@[expose] noncomputable def rPt (KP k i : Nat) : Nat :=
  fld(KP, Nat.add (Nat.mul (nat_lit 264) k) (Nat.mul (nat_lit 12) i), nat_lit 4095)

@[expose] noncomputable def rKey (KP k : Nat) : Nat :=
  fld(KP, Nat.mul (nat_lit 264) k,
    Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 264)) (nat_lit 1))

@[expose] noncomputable def rPar (PL k : Nat) : Nat := fld(PL, Nat.mul (nat_lit 32) k, nat_lit 4095)

@[expose] noncomputable def rLab (PL k : Nat) : Nat :=
  fld(PL, Nat.add (Nat.mul (nat_lit 32) k) (nat_lit 12), nat_lit 31)

@[expose] noncomputable def rDep (PL k : Nat) : Nat :=
  fld(PL, Nat.add (Nat.mul (nat_lit 32) k) (nat_lit 17), nat_lit 1023)

@[expose] noncomputable def rPi (PI k i : Nat) : Nat :=
  fld(PI, Nat.add (Nat.mul (nat_lit 128) k) (Nat.mul (nat_lit 5) i), nat_lit 31)

@[expose] noncomputable def ptsK (KP k : Nat) : Bool :=
  bAnd(allN (nat_lit 21) fun i => Nat.blt (rPt KP k i) (rPt KP k (Nat.succ i)),
    Nat.blt (rPt KP k (nat_lit 21)) (nat_lit 3510))

@[expose] noncomputable def rootK (UL gw : List Nat) (KP PL PI k : Nat) : Bool :=
  bAnd(Nat.beq (rDep PL k) (nat_lit 0), allN (nat_lit 22) fun i => strictB (rPi PI k i) fun j =>
    bAnd(Nat.blt j (nat_lit 22), Nat.beq (rPt KP k i) (wAp LT gw (gD UL j))))

@[expose] noncomputable def edgeK (N KP PL PI k : Nat) : Bool :=
  strictB (rPar PL k) fun p => strictB (rLab PL k) fun l =>
    bAnd(Nat.blt p N, bAnd(Nat.beq (rDep PL k) (Nat.succ (rDep PL p)),
      bAnd(Nat.blt l (nat_lit 32), bAnd(Nat.beq (LT l (nat_lit 0)) (nat_lit 0),
        allN (nat_lit 22) fun i => strictB (rPi PI k i) fun j =>
          bAnd(Nat.blt j (nat_lit 22), Nat.beq (rPt KP k i) (LT l (rPt KP p j)))))))

@[expose] noncomputable def rowK (UL gw : List Nat) (N root KP PL PI k : Nat) : Bool :=
  bAnd(ptsK KP k, bIf(Nat.beq k root, rootK UL gw KP PL PI k, edgeK N KP PL PI k))

@[expose] noncomputable def rowsK (UL gw : List Nat) (N root KP PL PI lo cnt : Nat) : Bool :=
  allN cnt fun k => rowK UL gw N root KP PL PI (Nat.add lo k)

@[expose] noncomputable def keysK (N KP : Nat) : Bool :=
  allN (Nat.sub N (nat_lit 1)) fun k => Nat.blt (rKey KP k) (rKey KP (Nat.succ k))

@[expose] noncomputable def ulK (UL : List Nat) : Bool :=
  bAnd(Nat.beq UL.length (nat_lit 22), bAnd(allN (nat_lit 21) fun i =>
    Nat.blt (gD UL i) (gD UL (Nat.succ i)), Nat.blt (gD UL (nat_lit 21)) (nat_lit 3510)))

@[expose] noncomputable def headK (UL gw : List Nat) (N root KP : Nat) : Bool :=
  bAnd(ulK UL, bAnd(lettersLt (nat_lit 32) gw, bAnd(Nat.beq (wAp LT gw (gD UL (nat_lit 0)))
    (nat_lit 0), bAnd(Nat.blt root N, keysK N KP))))

@[expose] noncomputable def treeK (UL gw : List Nat) (N root KP PL PI : Nat) : Bool :=
  bAnd(headK UL gw N root KP, rowsK UL gw N root KP PL PI (nat_lit 0) N)

@[expose] noncomputable def itP (f : Nat → Nat) (o x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x) (fun _ ih x => strictN (f x) ih) o x

@[expose] noncomputable def BS (i : Nat) : Nat := gD [0, 1, 6, 11, 3] i

@[expose] noncomputable def ordK (w1 w2 : List Nat) : Bool :=
  bAnd(lettersLt (nat_lit 2) w1, bAnd(lettersLt (nat_lit 2) w2, allN (nat_lit 5) fun b =>
    strictB (BS b) fun x => bAnd(Nat.beq (itP (wAp AB w1) (nat_lit 5) x) x,
      Nat.beq (itP (wAp AB w2) (nat_lit 14) x) x)))

@[expose] noncomputable def traceK (UL w1 w2 p1 p2 : List Nat) : Bool :=
  allN (nat_lit 22) fun i => strictB (gD UL i) fun x =>
    strictB (gD p1 i) fun j1 => strictB (gD p2 i) fun j2 =>
      bAnd(Nat.blt j1 (nat_lit 22), bAnd(Nat.blt j2 (nat_lit 22),
        bAnd(Nat.beq (wAp AB w1 x) (gD UL j1), Nat.beq (wAp AB w2 (wAp AB w2 x)) (gD UL j2))))

@[expose] noncomputable def PP (p1 p2 : List Nat) (c j : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), gD p1 j, gD p2 j)

@[expose] noncomputable def lvS (i : Nat) : Nat := gD [22, 21, 20, 16, 3] i

@[expose] noncomputable def levelK (p1 p2 : List Nat) (W : List (List Nat)) (O P G : List Nat)
    (i : Nat) : Bool :=
  strictB (lvS i) fun s =>
  bAnd(List.all W (lettersLt (nat_lit 2)),
  bAnd(List.all W (fun w => allN i fun j => Nat.beq (wAp (PP p1 p2) w j) j),
  bAnd(Nat.beq O.length s, bAnd(Nat.beq P.length s, bAnd(Nat.beq G.length s,
  bAnd(Nat.beq (gD O (nat_lit 0)) i,
  bAnd(allN s (fun a => Nat.blt (gD O a) (nat_lit 22)),
  bAnd(allN s (fun a => allN a fun b => Bool.not (Nat.beq (gD O a) (gD O b))),
  allN (Nat.sub s (nat_lit 1)) fun a0 => strictB (Nat.succ a0) fun a =>
    strictB (gD P a) fun p => strictB (gD G a) fun c =>
      bAnd(Nat.blt p a, bAnd(Nat.blt c W.length,
        Nat.beq (gD O a) (wAp (PP p1 p2) (List.getD W c []) (gD O p))))))))))))

@[expose] noncomputable def chainK (p1 p2 : List Nat) (lvW : List (List (List Nat)))
    (lvO lvP lvG : List (List Nat)) : Bool :=
  allN (nat_lit 5) fun i => levelK p1 p2 (List.getD lvW i []) (List.getD lvO i [])
    (List.getD lvP i []) (List.getD lvG i []) i

end CFSG.KS.Fi22Gen

end
