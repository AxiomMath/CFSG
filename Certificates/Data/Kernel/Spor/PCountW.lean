module

public import Certificates.Data.Kernel.Spor.PCount
public import Mathlib.Logic.Equiv.Defs

public section

namespace CFSG.KS.PCnt

open CFSG.KC.Enum

@[expose] noncomputable def ordFour (n w m I x : Nat) : Nat :=
  strictN (pcomp n w m x x) (fun s =>
    nIf(Nat.beq s I, nat_lit 0, nIf(Nat.beq (pcomp n w m s s) I, nat_lit 1, nat_lit 0)))

@[expose] noncomputable def ordPr (n w m I x k : Nat) : Nat :=
  nIf(Nat.beq x I, nat_lit 0, nIf(Nat.beq (ppw n w m x k) I, nat_lit 1, nat_lit 0))

@[expose] noncomputable def partnerW (n w m I X y : Nat) : Nat :=
  nIf(Nat.beq (ordFour n w m I y) (nat_lit 1),
    strictN (pcomp n w m X y) (fun z =>
      nIf(Nat.beq (ordPr n w m I (pcomp n w m z y) (nat_lit 4)) (nat_lit 1),
        nIf(Nat.beq (ordPr n w m I z (nat_lit 10)) (nat_lit 1),
          ordSix n w m I (pcomp n w m (pcomp n w m z X) (pcomp n w m (pcomp n w m y y) y)),
          nat_lit 0),
        nat_lit 0)),
    nat_lit 0)

@[expose] noncomputable def cntW (n w m I X y : Nat) : Nat :=
  Nat.add (ordTwo n w m I y) (Nat.mul (nat_lit 1048576) (partnerW n w m I X y))

abbrev DState := List Nat × List Nat

@[expose] noncomputable def dIf (c : Bool) (t e : DState) : DState :=
  Bool.rec (motive := fun _ => DState) e t c

@[expose] noncomputable def dAdd (z : Nat) (s : DState) : DState :=
  dIf (memB z s.1) s (z :: s.1, z :: s.2)

@[expose] noncomputable def dStep (n w m A Ai B Bi : Nat) (s : DState) : DState :=
  List.rec (motive := fun _ => DState) s
    (fun e rest _ => dAdd (cjP n w m B Bi e) (dAdd (cjP n w m A Ai e) (s.1, rest))) s.2

@[expose] noncomputable def conjDFS (n w m A Ai B Bi r fuel : Nat) : List Nat :=
  (Nat.rec (motive := fun _ => DState) ([r], [r]) (fun _ ih => dStep n w m A Ai B Bi ih) fuel).1

@[expose] def baseOK {n : Nat} : List (List (Equiv.Perm (Fin n))) → List (Fin n) → Bool
  | [], [] => true
  | T :: Ts, b :: bs =>
    decide (T.map fun t => t b).Nodup && Ts.all (fun T' => T'.all fun t => decide (t b = b)) &&
      baseOK Ts bs
  | _, _ => false

end CFSG.KS.PCnt

end
