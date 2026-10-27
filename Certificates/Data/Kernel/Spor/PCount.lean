module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.PCnt

open CFSG.KC.Enum

@[expose] noncomputable def pRow (n w m : Nat) (k : Nat → Nat → Nat) (g : Nat) :
    List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun t _ ih acc => strictN (pcomp n w m g t) (fun h => strictN (k h acc) ih))

@[expose] noncomputable def pcnt (n w m : Nat) (F : Nat → Nat) :
    List (List Nat) → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun g acc => Nat.add acc (F g))
    (fun T _ ih g acc => pRow n w m ih g T acc)

@[expose] noncomputable def ppw (n w m x : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ ih => strictN ih (fun y => pcomp n w m x y))

@[expose] noncomputable def ordTwo (n w m I x : Nat) : Nat :=
  nIf(Nat.beq x I, nat_lit 0, nIf(Nat.beq (pcomp n w m x x) I, nat_lit 1, nat_lit 0))

@[expose] noncomputable def ordThree (n w m I x : Nat) : Nat :=
  nIf(Nat.beq x I, nat_lit 0,
    nIf(Nat.beq (pcomp n w m x (pcomp n w m x x)) I, nat_lit 1, nat_lit 0))

@[expose] noncomputable def ordSix (n w m I c : Nat) : Nat :=
  nIf(Nat.beq (ppw n w m c (nat_lit 5)) I,
    nIf(Nat.beq (ppw n w m c (nat_lit 1)) I, nat_lit 0,
      nIf(Nat.beq (ppw n w m c (nat_lit 2)) I, nat_lit 0, nat_lit 1)), nat_lit 0)

@[expose] noncomputable def partner (n w m I X y : Nat) : Nat :=
  nIf(Nat.beq (ordThree n w m I y) (nat_lit 1),
    strictN (pcomp n w m X y) (fun z =>
      nIf(Nat.beq z I, nat_lit 0,
        nIf(Nat.beq (ppw n w m z (nat_lit 10)) I,
          strictN (pcomp n w m (pcomp n w m z X) (pcomp n w m y y)) (fun c => ordSix n w m I c),
          nat_lit 0))),
    nat_lit 0)

@[expose] noncomputable def cnt4 (n w m I X₁ X₂ y : Nat) : Nat :=
  Nat.add (ordTwo n w m I y) (Nat.add (Nat.mul (nat_lit 1048576) (ordThree n w m I y))
    (Nat.add (Nat.mul (nat_lit 1099511627776) (partner n w m I X₁ y))
      (Nat.mul (nat_lit 1152921504606846976) (partner n w m I X₂ y))))

@[expose] noncomputable def memB (x : Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq x a, true, ih))

@[expose] noncomputable def distB : List Nat → Bool :=
  List.rec (motive := fun _ => Bool) true (fun a t ih => bIf(memB a t, false, ih))

@[expose] noncomputable def getN : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih i => Nat.rec (motive := fun _ => Nat) a (fun j _ => ih j) i)

@[expose] noncomputable def cjP (n w m G Gi x : Nat) : Nat := pcomp n w m (pcomp n w m G x) Gi

@[expose] noncomputable def conjTreeP (n w m A Ai B Bi r : Nat) (K P Lb : List Nat) : Bool :=
  allN K.length (fun k => bIf(Nat.beq k (nat_lit 0), Nat.beq (getN K (nat_lit 0)) r,
    bAnd(Nat.blt (getN P k) k,
      Nat.beq (getN K k) (nIf(Nat.beq (getN Lb k) (nat_lit 0),
        cjP n w m A Ai (getN K (getN P k)), cjP n w m B Bi (getN K (getN P k)))))))

abbrev BState := List Nat × List Nat × List Nat

@[expose] noncomputable def sIf (c : Bool) (t e : BState) : BState := Bool.rec (motive := fun _ => BState) e t c

@[expose] noncomputable def bAdd (z h l : Nat) (s : BState) : BState :=
  sIf (memB z s.1) s (s.1 ++ [z], s.2.1 ++ [h], s.2.2 ++ [l])

@[expose] noncomputable def bfsStep (n w m A Ai B Bi h : Nat) (s : BState) : BState :=
  sIf (Nat.blt h s.1.length)
    (bAdd (cjP n w m B Bi (getN s.1 h)) h (nat_lit 1)
      (bAdd (cjP n w m A Ai (getN s.1 h)) h (nat_lit 0) s)) s

@[expose] noncomputable def bfsRun (n w m A Ai B Bi : Nat) (fuel : Nat) : Nat → BState → BState :=
  Nat.rec (motive := fun _ => Nat → BState → BState) (fun _ s => s)
    (fun _ ih h s => List.rec (motive := fun _ => BState) (ih (Nat.succ h) (bfsStep n w m A Ai B Bi h s))
      (fun _ _ _ => ih (Nat.succ h) (bfsStep n w m A Ai B Bi h s)) s.1) fuel

@[expose] noncomputable def conjBFS (n w m A Ai B Bi r fuel : Nat) : BState :=
  bfsRun n w m A Ai B Bi fuel (nat_lit 0) ([r], [nat_lit 0], [nat_lit 0])

end CFSG.KS.PCnt

end
