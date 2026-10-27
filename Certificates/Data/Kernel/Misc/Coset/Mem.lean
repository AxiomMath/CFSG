module

public import CFSG.Certificates.Kernel.Bounds.Core

public section

namespace CFSG.KC.MiscCoset.Mem

@[expose] noncomputable def invC (a : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.pred a) (Nat.succ a) (Nat.beq (Nat.mod a 2) 0)

@[expose] noncomputable def memWalk (F : Nat → Nat) (f : Nat) (w : List Nat) : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ cur => cur)
    (fun a _ ih refs cur => List.rec (motive := fun _ => Nat) CFSG.Certificates.KB.bad
      (fun r rest _ => ih rest (CFSG.Certificates.KB.refStep F f r a (invC a) cur)) refs) w

@[expose] noncomputable def memOK (F : Nat → Nat) (f : Nat) (w refs : List Nat) : Bool :=
  Nat.beq (memWalk F f w refs 0) 0

end CFSG.KC.MiscCoset.Mem

end
