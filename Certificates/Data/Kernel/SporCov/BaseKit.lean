module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.SporCov

open CFSG.KC.Loop

@[expose] noncomputable def letB (fA fAi fB fBi : Nat → Nat) (c x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (fBi x) (fB x) (Nat.beq c (nat_lit 2)))
      (fAi x) (Nat.beq c (nat_lit 1)))
    (fA x) (Nat.beq c (nat_lit 0))

@[expose] noncomputable def imB (fA fAi fB fBi : Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun c _ ih x => strictN (letB fA fAi fB fBi c x) ih) w x

@[expose] noncomputable def eqB (fA fAi fB fBi : Nat → Nat) (bs : List Nat) (u v : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.beq (imB fA fAi fB fBi u b) (imB fA fAi fB fBi v b), ih)) bs

@[expose] noncomputable def letP (c : Nat) : Bool := Nat.blt c (nat_lit 4)

end CFSG.KC.SporCov

end
