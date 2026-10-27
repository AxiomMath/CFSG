module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.BaseEq

open CFSG.KC.Enum

@[expose] noncomputable def allL (ps : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun p _ ih => bAnd(f p, ih)) ps

@[expose] noncomputable def left2K (w m : Nat) (ps : List Nat) (a b c : Nat) : Bool :=
  allL ps fun p => Nat.beq (pg w m a (pg w m b p)) (pg w m c p)

@[expose] noncomputable def conj3K (w m : Nat) (ps : List Nat) (a b ai c : Nat) : Bool :=
  allL ps fun p => Nat.beq (pg w m a (pg w m b (pg w m ai p))) (pg w m c p)

@[expose] noncomputable def sqFixK (w m : Nat) (ps : List Nat) (b : Nat) : Bool :=
  allL ps fun p => Nat.beq (pg w m b (pg w m b p)) p

@[expose] noncomputable def cntN (n : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => strictN ih (fun a => Nat.add a (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (nat_lit 1) (f i)))) n

end CFSG.KS.BaseEq

end
