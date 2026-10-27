module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.RelTab

@[expose] noncomputable def prodAcc (mm : Nat → Nat → Nat) (M : Nat → Nat) : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a) (fun j _ ih a => ih (mm a (M j)))

@[expose] noncomputable def prodL (mm : Nat → Nat → Nat) (one : Nat) (M : Nat → Nat) :
    List Nat → Nat :=
  List.rec (motive := fun _ => Nat) one (fun f fs _ => prodAcc mm M fs (M f))

@[expose] noncomputable def relRow (mm : Nat → Nat → Nat) (one : Nat) (G X M : Nat → Nat)
    (l i : Nat) (fs : List Nat) : Bool :=
  Nat.beq (mm (G l) (X i)) (mm (prodL mm one M fs) (G l))

@[expose] noncomputable def relTab (mm : Nat → Nat → Nat) (one : Nat) (G X M : Nat → Nat) :
    List (Nat × Nat × List Nat) → Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => bAnd(relRow mm one G X M r.1 r.2.1 r.2.2, ih))

end CFSG.KC.RelTab

end
