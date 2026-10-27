module

public import Certificates.Data.Kernel.Census.Packed

public section

namespace CFSG.KC.Q16Q16K

open CFSG.KC.Census

abbrev Rec := Nat × Nat × Nat

@[expose] noncomputable def allL (f : Rec → Bool) (L : List Rec) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(f a, ih)) L

@[expose] noncomputable def cm (n w a b : Nat) : Bool := Nat.beq (pc n w a b) (pc n w b a)

@[expose] noncomputable def recOK (n w : Nat) (r : Rec) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight r.1 (Nat.mul n w)) (nat_lit 0),
    bAnd(Nat.beq r.2.1 (pc n w r.1 r.1), Nat.beq r.2.2 (pc n w r.2.1 r.2.1)))

@[expose] noncomputable def chkL (n w x y k f : Nat) (r : Rec) : Bool :=
  bIf(Nat.beq r.2.1 f, bIf(Nat.beq (pc n w k (pc n w r.1 k)) r.1,
    bIf(cm n w x r.1, bIf(cm n w y r.1, false, true), true), true), true)

@[expose] noncomputable def chkK (n w : Nat) (L : List Rec) (x y f : Nat) (r : Rec) : Bool :=
  bIf(Nat.beq r.2.2 f, bIf(cm n w x r.1, bIf(cm n w y r.1,
    allL (chkL n w x y r.1 f) L, true), true), true)

@[expose] noncomputable def chkY (n w : Nat) (L : List Rec) (x f : Nat) (r : Rec) : Bool :=
  bIf(Nat.beq r.2.1 f, bIf(Nat.beq (pc n w x (pc n w r.1 x)) r.1,
    allL (chkK n w L x r.1 f) L, true), true)

@[expose] noncomputable def chkX (n w : Nat) (L : List Rec) (r : Rec) : Bool :=
  bIf(Nat.beq r.2.2 (pid n w), true,
    bIf(Nat.beq (pc n w r.2.2 r.2.2) (pid n w), allL (chkY n w L r.1 r.2.2) L, true))

@[expose] noncomputable def mkRec (n w x : Nat) : Rec :=
  (x, pc n w x x, pc n w (pc n w x x) (pc n w x x))

end CFSG.KC.Q16Q16K

end
