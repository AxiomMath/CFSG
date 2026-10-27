module

public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.KC.VecK

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2

@[expose] noncomputable def lk (T : Nat → Nat) (w i : Nat) : Nat := fget (T i) (Nat.land i (nat_lit 63)) w

@[expose] noncomputable def getF (L : List (Nat → Nat)) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun a _ ih i => Nat.rec (motive := fun _ => Nat → Nat) a (fun j _ => ih j) i) L

@[expose] noncomputable def seedK (csA csB : List Char) (d MA MB NA NB expA expB : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) d) (andB (Nat.blt d (nat_lit 64))
  (andB (Nat.blt (nat_lit 0) expA) (andB (Nat.blt (nat_lit 0) expB)
  (andB (m1Bind csA d MA) (andB (m1Bind csB d MB)
  (andB (Nat.beq (trK d MA) NA) (andB (Nat.beq (trK d MB) NB)
  (andB (Nat.beq (powK d MA expA) (idF d)) (Nat.beq (powK d MB expB) (idF d))))))))))

@[expose] noncomputable def orbAt (d n NA NB : Nat) (P AT BT : Nat → Nat) (h : Nat) : Bool :=
  strictB (lk P (nat_lit 32) h) fun v => strictB (lk AT (nat_lit 32) h) fun a =>
    strictB (lk BT (nat_lit 32) h) fun b =>
      andB (Nat.blt v (pw2 d)) (andB (Nat.blt a n) (andB (Nat.blt b n)
        (andB (Nat.beq (lk P (nat_lit 32) a) (vmF d NA v)) (Nat.beq (lk P (nat_lit 32) b) (vmF d NB v)))))

@[expose] noncomputable def seqAt (AT BT : Nat → Nat) (k : Nat) : Nat :=
  nIf(Nat.beq (Nat.land k (nat_lit 1)) (nat_lit 0), lk AT (nat_lit 32) (Nat.shiftRight k (nat_lit 1)),
    lk BT (nat_lit 32) (Nat.shiftRight k (nat_lit 1)))

@[expose] noncomputable def bfsAt (n : Nat) (AT BT FO : Nat → Nat) (h : Nat) : Bool :=
  andB (orB (Nat.beq h (nat_lit 0)) (strictB (lk FO (nat_lit 32) h) fun f =>
      andB (Nat.blt f (Nat.mul (nat_lit 2) h)) (andB (Nat.beq (seqAt AT BT f) h)
        (orB (Nat.ble n (Nat.succ h)) (Nat.blt f (lk FO (nat_lit 32) (Nat.succ h)))))))
    (andB (strictB (lk AT (nat_lit 32) h) fun x =>
        orB (Nat.beq x (nat_lit 0)) (Nat.ble (lk FO (nat_lit 32) x) (Nat.mul (nat_lit 2) h)))
      (strictB (lk BT (nat_lit 32) h) fun x =>
        orB (Nat.beq x (nat_lit 0)) (Nat.ble (lk FO (nat_lit 32) x) (Nat.succ (Nat.mul (nat_lit 2) h)))))

@[expose] noncomputable def allS (lo cnt : Nat) (f : Nat → Bool) : Bool :=
  allN cnt fun i => f (Nat.add lo i)

@[expose] noncomputable def sliceN (n S s : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.sub n (Nat.mul s S)) S (Nat.ble (Nat.mul (Nat.succ s) S) n)

@[expose] noncomputable def allL {α : Type} (f : α → Bool) (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => andB (f a) ih) L

@[expose] noncomputable def eqL (L M : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun M => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) M)
    (fun a _ ih M => List.rec (motive := fun _ => Bool) false (fun b M' _ => andB (Nat.beq a b) (ih M')) M)
    L M

@[expose] noncomputable def sortAt (n : Nat) (P S IP SP : Nat → Nat) (h : Nat) : Bool :=
  strictB (lk IP (nat_lit 32) h) fun k =>
    andB (Nat.blt k n) (andB (Nat.beq (lk S (nat_lit 32) k) (lk P (nat_lit 32) h))
      (andB (Nat.beq (lk SP (nat_lit 32) k) h)
        (orB (Nat.ble n (Nat.succ h)) (Nat.blt (lk S (nat_lit 32) h) (lk S (nat_lit 32) (Nat.succ h))))))

@[expose] noncomputable def letAt (d n N : Nat) (P T : Nat → Nat) (h : Nat) : Bool :=
  strictB (lk T (nat_lit 32) h) fun q =>
    andB (Nat.blt q n) (Nat.beq (lk P (nat_lit 32) q) (vmF d N (lk P (nat_lit 32) h)))

@[expose] noncomputable def letN (NA NAi NB NBi : Nat) (z : Int) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun k => nIf(Nat.beq k (nat_lit 1), NA, nIf(Nat.beq k (nat_lit 2), NB, NBi)))
    (fun k => nIf(Nat.beq k (nat_lit 0), NAi, NBi)) z

@[expose] noncomputable def wordN (d NA NAi NB NBi : Nat) (w : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) (idF d)
    (fun z _ ih => strictN ih fun x => mulF d x (letN NA NAi NB NBi z)) w

@[expose] noncomputable def setL (R : List Nat) (k x : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun a rest ih j => Nat.rec (motive := fun _ => List Nat) (List.cons x rest)
      (fun j' _ => List.cons a (ih j')) j) R k

@[expose] noncomputable def stepN (d : Nat) (ins : CFSG.Sporadic.Th.Native.Instr)
    (st : List Nat × List Nat × Bool) : List Nat × List Nat × Bool :=
  Prod.rec (motive := fun _ => List Nat × List Nat × Bool) (fun R rest => Prod.rec
    (motive := fun _ => List Nat × List Nat × Bool) (fun V ok =>
      CFSG.Sporadic.Th.Native.Instr.rec (motive := fun _ => List Nat × List Nat × Bool)
        (fun i j k => (setL R k (mulF d (getL (idF d) R j) (getL (idF d) R i)), V, ok))
        (fun e i k => (setL R k (powK d (getL (idF d) R i) e), V, ok))
        (fun i k => List.rec (motive := fun _ => List Nat × List Nat × Bool) (R, V, false)
          (fun x V' _ => (setL R k x, V',
            andB ok (Nat.beq (mulF d (getL (idF d) R i) x) (idF d)))) V) ins) rest) st

@[expose] noncomputable def slpN (d : Nat) (prog : List CFSG.Sporadic.Th.Native.Instr)
    (R V : List Nat) : List Nat × List Nat × Bool :=
  List.rec (motive := fun _ => List Nat × List Nat × Bool → List Nat × List Nat × Bool)
    (fun st => st) (fun ins _ ih st => ih (stepN d ins st)) prog (R, V, true)

@[expose] noncomputable def slpOK (d : Nat) (prog : List CFSG.Sporadic.Th.Native.Instr)
    (R0 V R : List Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun R' rest => Prod.rec (motive := fun _ => Bool)
    (fun _ ok => andB ok (eqL R' R)) rest) (slpN d prog R0 V)

@[expose] noncomputable def basisK (d BI BM : Nat) (P Q : Nat → Nat) : Bool :=
  andB (allN d fun i => Nat.beq (fget BM i d) (lk P (nat_lit 32) (Q i)))
    (Nat.beq (mulF d BI BM) (idF d))

@[expose] noncomputable def instrLtK (r : Nat) (ins : CFSG.Sporadic.Th.Native.Instr) : Bool :=
  CFSG.Sporadic.Th.Native.Instr.rec (motive := fun _ => Bool)
    (fun i j k => andB (Nat.blt i r) (andB (Nat.blt j r) (Nat.blt k r)))
    (fun _ i k => andB (Nat.blt i r) (Nat.blt k r)) (fun i k => andB (Nat.blt i r) (Nat.blt k r)) ins

@[expose] noncomputable def regs0N (d nregs W0 W1 : Nat) : List Nat :=
  List.cons W0 (List.cons W1 (Nat.rec (motive := fun _ => List Nat) List.nil
    (fun _ ih => List.cons (idF d) ih) (Nat.sub nregs (nat_lit 2))))

@[expose] noncomputable def lettersK (d : Nat) (R : List Nat) (sel : List Nat) (LM : List Nat) : Bool :=
  andB (Nat.beq (lenL LM) (Nat.mul (nat_lit 2) (lenL sel)))
    (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun s _ ih j => strictB (getL (nat_lit 0) LM (Nat.mul (nat_lit 2) j)) fun x =>
        andB (Nat.beq x (getL (idF d) R s))
          (andB (Nat.beq (mulF d x (getL (nat_lit 0) LM (Nat.succ (Nat.mul (nat_lit 2) j)))) (idF d))
            (ih (Nat.succ j)))) sel (nat_lit 0))

@[expose] noncomputable def fixB (LT : Nat → Nat → Nat) (B : Nat → Nat) (i l : Nat) : Bool :=
  allN i fun k => strictB (B k) fun b => Nat.beq (lk (LT l) (nat_lit 32) b) b

@[expose] noncomputable def treeAt (n kL m i r : Nat) (LT : Nat → Nat → Nat) (B Ot IX Op Ol : Nat → Nat)
    (t : Nat) : Bool :=
  strictB (lk Ot (nat_lit 32) t) fun p => andB (Nat.blt p n)
    (andB (Nat.beq (lk IX (nat_lit 32) p) t)
    (andB (allN (Nat.div kL (nat_lit 2)) fun j => strictB (Nat.mul (nat_lit 2) j) fun l =>
        orB (notB (fixB LT B i l)) (strictB (lk (LT l) (nat_lit 32) p) fun q =>
        strictB (lk IX (nat_lit 32) q) fun x => andB (Nat.blt x m) (Nat.beq (lk Ot (nat_lit 32) x) q)))
      (bIf(Nat.beq t (nat_lit 0), Nat.beq p r,
        strictB (lk Op (nat_lit 32) t) fun u => strictB (lk Ol (nat_lit 32) t) fun l =>
          andB (Nat.blt u t) (andB (Nat.blt l kL) (andB (fixB LT B i l)
            (Nat.beq (lk (LT l) (nat_lit 32) (lk Ot (nat_lit 32) u)) p)))))))

@[expose] noncomputable def subAt (n kL m j r : Nat) (LT : Nat → Nat → Nat) (B St LB PS Sp Sl : Nat → Nat)
    (t : Nat) : Bool :=
  strictB (lk St (nat_lit 32) t) fun p => andB (Nat.blt p n)
    (andB (Nat.beq (lk LB (nat_lit 32) p) j) (andB (Nat.beq (lk PS (nat_lit 32) p) t)
    (andB (allN (Nat.div kL (nat_lit 2)) fun k => strictB (Nat.mul (nat_lit 2) k) fun l =>
      orB (notB (fixB LT B (nat_lit 1) l)) (strictB (lk (LT l) (nat_lit 32) p) fun q =>
        andB (Nat.beq (lk LB (nat_lit 32) q) j)
          (strictB (lk PS (nat_lit 32) q) fun x => andB (Nat.blt x m) (Nat.beq (lk St (nat_lit 32) x) q))))
      (bIf(Nat.beq t (nat_lit 0), Nat.beq p r,
        strictB (lk Sp (nat_lit 32) t) fun u => strictB (lk Sl (nat_lit 32) t) fun l =>
          andB (Nat.blt u t) (andB (Nat.blt l kL) (andB (fixB LT B (nat_lit 1) l)
            (Nat.beq (lk (LT l) (nat_lit 32) (lk St (nat_lit 32) u)) p))))))))

@[expose] noncomputable def labAt (k : Nat) (sizes : List Nat) (STs : List (Nat → Nat)) (LB PS : Nat → Nat)
    (p : Nat) : Bool :=
  strictB (lk LB (nat_lit 32) p) fun j => strictB (lk PS (nat_lit 32) p) fun x =>
    andB (Nat.blt j k) (andB (Nat.blt x (getL (nat_lit 0) sizes j))
      (Nat.beq (lk (getF STs j) (nat_lit 32) x) p))

@[expose] noncomputable def fixQ (d N q : Nat) (P Q : Nat → Nat) : Bool :=
  allN q fun t => strictB (lk P (nat_lit 32) (Q t)) fun v => Nat.beq (vmF d N v) v

@[expose] noncomputable def ordK (d N q : Nat) (P Q : Nat → Nat) (p e : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) e) (andB (fixQ d (powK d N (Nat.pow p e)) q P Q)
    (notB (fixQ d (powK d N (Nat.pow p (Nat.sub e (nat_lit 1)))) q P Q)))

end CFSG.KC.VecK

end
