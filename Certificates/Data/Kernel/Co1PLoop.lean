module

public import Certificates.Data.Kernel.Co1P

public section

namespace CFSG.KC.Co1P

open CFSG.KLie.CT

@[expose] noncomputable def chunkK (N : Nat) (f : Nat → Bool) (c : Nat) : Bool :=
  allN (nat_lit 64) fun k => (fun i => CFSG.KLie.CT.orB (Nat.ble N i) (f i)) (Nat.add (Nat.mul (nat_lit 64) c) k)

@[expose] noncomputable def eqLK : List Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun ys => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ys)
    (fun x _ ih ys => List.rec (motive := fun _ => Bool) false
      (fun y ys' _ => CFSG.KLie.CT.andB (Nat.beq x y) (ih ys')) ys)

end CFSG.KC.Co1P

end
