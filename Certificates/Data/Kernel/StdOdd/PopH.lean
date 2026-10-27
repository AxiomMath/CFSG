module

public import Certificates.Data.Kernel.StdOdd.Chain

public section

namespace CFSG.KC.StdOdd.Chain

open CFSG.KC.StdOdd.Orbit

@[expose] noncomputable def popH (d x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => Nat.land x 1)
    (fun d ih x => Bool.rec (motive := fun _ => Nat)
      (forceN (Nat.shiftLeft 1 d) fun sh =>
        forceN (Nat.land x (Nat.sub (Nat.shiftLeft 1 sh) 1)) fun lo =>
        forceN (Nat.shiftRight x sh) fun hi => Nat.add (ih lo) (ih hi))
      (nat_lit 0) (Nat.beq x 0)) d x

@[expose] noncomputable def popHB (d x c : Nat) : Bool :=
  andB (Nat.beq (Nat.shiftRight x (Nat.shiftLeft 1 d)) 0) (Nat.beq (popH d x) c)

end CFSG.KC.StdOdd.Chain
