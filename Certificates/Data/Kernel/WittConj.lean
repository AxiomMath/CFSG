module

public import Certificates.Data.Kernel.WittCnt

public section

namespace CFSG.KC.WCnt

open CFSG.KC.Enum

@[expose] noncomputable def invT (I y : Nat) : Bool :=
  Nat.beq (pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) y y) I

@[expose] noncomputable def memN (Ls : List Nat) (y : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun L _ ih => bIf(Nat.beq y L, true, ih)) Ls

@[expose] noncomputable def conjR (G y : Nat) (Rs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun R _ ih =>
    bIf(Nat.beq (pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) G y)
      (pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) R G), true, ih)) Rs

@[expose] noncomputable def conjAny (Gs Rs : List Nat) (y : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun G _ ih => bIf(conjR G y Rs, true, ih)) Gs

@[expose] noncomputable def eqL : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, y :: ys => bAnd(Nat.beq x y, eqL xs ys)
  | _, _ => false

@[expose] noncomputable def pwordAB (A B Bi G : Nat) (l : List Char) : Nat :=
  l.foldl (fun G c => pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) G
    (if c = 'a' then A else if c = 'b' then B else Bi)) G

@[expose] noncomputable def pevalW (P PI : List Nat) (I : Nat) (w : List (Fin 5 × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) I (fun x _ ih =>
    pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31)
      (Bool.rec (motive := fun _ => Nat) (PI.getD x.1.val 0) (P.getD x.1.val 0) x.2) ih) w

end CFSG.KC.WCnt

end
