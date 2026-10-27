module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Orders.Mat

public section

namespace CFSG.KC.Fi24Fix

open CFSG.KC.Loop CFSG.KC.Ord

@[expose] noncomputable def wordMul (mul : Nat → Nat → Nat) (RB : Nat → Nat) (w : List Nat)
    (Y : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) Y (fun k _ ih => mul (RB k) ih) w

@[expose] noncomputable def keepsOK (mul : Nat → Nat → Nat) (Q X : Nat) : Bool :=
  Nat.beq (strictN (mul X Q) (fun Z => nIf(Nat.beq (mul Q Z) Z, nat_lit 1, nat_lit 0))) (nat_lit 1)

@[expose] noncomputable def ascOK (S : Nat → Nat) (n b : Nat) : Bool :=
  andB (Nat.ble (nat_lit 1) (S (nat_lit 0))) (andB (Nat.blt (S (Nat.sub n (nat_lit 1))) b)
    (allBelow (Nat.sub n (nat_lit 1)) (Nat.add (Nat.shiftRight n (nat_lit 6)) (nat_lit 1))
      (fun i => Nat.blt (S i) (S (Nat.succ i)))))

end CFSG.KC.Fi24Fix

end
