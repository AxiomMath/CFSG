module

public import Certificates.Data.Kernel.Misc.Coset.Act

public section

namespace CFSG.KC.MiscCoset.Act

@[expose] noncomputable def downAt (A : Nat → Nat) (L n x : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun c ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.blt (step A L x c) x)) n

@[expose] noncomputable def fixAll (A : Nat → Nat) (L : Nat) (us : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun u _ ih => andB (fixOK A L u) ih) us

end CFSG.KC.MiscCoset.Act

end
