module

public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.XorSel

open CFSG.KLie.CT

@[expose] noncomputable def selK (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun e _ ih c => Nat.xor (Bool.rec (motive := fun _ => Nat) (nat_lit 0) e (bit c (nat_lit 0)))
      (ih (Nat.shiftRight c (nat_lit 1)))) L

@[expose] noncomputable def selAllK (E : List Nat) (V : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun M => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) M)
    (fun v _ ih M => List.rec (motive := fun _ => Bool) false
      (fun m M' _ => andB (Nat.beq v (selK E m)) (ih M')) M) V

@[expose] noncomputable def pivGo (N : Nat) (P : List Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Bool)
    (fun pv _ => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) pv)
    (fun x _ ih pv lo => List.rec (motive := fun _ => Bool) false
      (fun p pv' _ => andB (Nat.ble lo p) (andB (Nat.blt p N) (andB (bit x p)
        (andB (Nat.beq (Nat.land x (Nat.sub (pw2 p) (nat_lit 1))) (nat_lit 0))
          (ih pv' (Nat.succ p)))))) pv) P

@[expose] noncomputable def pivOK (N : Nat) (P pv : List Nat) : Bool := pivGo N P pv (nat_lit 0)

end CFSG.KC.XorSel

end
