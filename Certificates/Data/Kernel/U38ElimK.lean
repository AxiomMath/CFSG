module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.U38Elim

@[expose] noncomputable def eAll (f : Nat → Bool) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) L

@[expose] noncomputable def eAny (f : Nat → Bool) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => bIf(f x, true, ih)) L

@[expose] noncomputable def eAnyN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => bIf(f i, true, ih)) n

@[expose] noncomputable def eMem (x : Nat) (L : List Nat) : Bool := eAny (fun y => Nat.beq y x) L

@[expose] noncomputable def eBit (M x : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight M x) (nat_lit 1)) (nat_lit 1)

end CFSG.KC.U38Elim

end
