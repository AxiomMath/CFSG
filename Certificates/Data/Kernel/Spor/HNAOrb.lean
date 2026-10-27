module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KS.HNA

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def stepK (n w m : Nat) (X A B : Nat → Nat) (t : Nat) : Bool :=
  bAnd(Nat.blt (A t) (Nat.add m t), bAnd(Nat.blt (B t) (Nat.add m t),
    Nat.beq (pcomp n w (mask w) (X (A t)) (X (B t))) (X (Nat.add m t))))

@[expose] noncomputable def stepSl (n w m : Nat) (X A B : Nat → Nat) (L s : Nat) : Bool :=
  allN L fun d => stepK n w m X A B (Nat.add (Nat.mul L s) d)

@[expose] noncomputable def commP (n w g h : Nat) : Nat :=
  pcomp n w (mask w) (pcomp n w (mask w) g h)
    (pcomp n w (mask w) (pinvS n w (mask w) g) (pinvS n w (mask w) h))

@[expose] noncomputable def poolK (n w R : Nat) (X P C : Nat → Nat) (f : Nat) : Bool :=
  bAnd(Nat.blt (P (Nat.mul 2 f)) R, bAnd(Nat.blt (P (Nat.succ (Nat.mul 2 f))) R,
    Nat.beq (C f) (commP n w (X (P (Nat.mul 2 f))) (X (P (Nat.succ (Nat.mul 2 f)))))))

@[expose] noncomputable def ord4K (n w I y : Nat) : Bool :=
  strictB (pcomp n w (mask w) y y) fun y2 =>
    bAnd(Bool.not (Nat.beq y2 I), Nat.beq (pcomp n w (mask w) y2 y2) I)

@[expose] noncomputable def witK (n w I : Nat) (T C Wc Wf Wm : Nat → Nat) (nc i : Nat) : Bool :=
  strictB (T i) fun x =>
    bIf(Nat.beq (Wc i) (nat_lit 0),
      Bool.not (bAnd(Bool.not (Nat.beq x I), Nat.beq (pcomp n w (mask w) x x) I)),
      bAnd(Nat.blt (Wf i) nc, ord4K n w I (ppow n w (mask w) I
        (pcomp n w (mask w) (commP n w x (C (Wf i))) I) (Wm i))))

@[expose] noncomputable def witSl (n w : Nat) (T C Wc Wf Wm : Nat → Nat) (nc L s : Nat) : Bool :=
  strictB (pidn n w) fun I => allN L fun d => witK n w I T C Wc Wf Wm nc (Nat.add (Nat.mul L s) d)

@[expose] noncomputable def listUp (F : Nat → Nat) (k : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih j => List.cons (F j) (ih (Nat.succ j))) k (nat_lit 0)

@[expose] noncomputable def wbRun (Wc Wf Wm : Nat → Nat) (N : Nat) (L : List Nat) :
    Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool)
    (fun ph i => bAnd(Nat.beq ph (nat_lit 0), Nat.beq i N))
    (fun x _ ih ph i =>
      bIf(Nat.beq ph (nat_lit 0),
        bIf(Nat.beq x (nat_lit 0), bAnd(Nat.beq (Wc i) (nat_lit 0), ih (nat_lit 0) (Nat.succ i)),
          bAnd(Bool.not (Nat.beq (Wc i) (nat_lit 0)), ih (nat_lit 1) i)),
      bIf(Nat.beq ph (nat_lit 1), bAnd(Nat.beq x (nat_lit 1), ih (nat_lit 2) i),
      bIf(Nat.beq ph (nat_lit 2), bAnd(Nat.beq x (Wf i), ih (nat_lit 3) i),
        bAnd(Nat.beq x (Wm i), ih (nat_lit 0) (Nat.succ i))))))
    L

end CFSG.KS.HNA

end
