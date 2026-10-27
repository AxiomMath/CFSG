module

public import Certificates.Data.Kernel.Spor.Fi24FiveK

public section

namespace CFSG.KC.Fi24FiveK

open CFSG.KC.Fi24PumpK CFSG.KC.Fi24Kn

@[expose] noncomputable def segC (R : List (List Nat)) (s n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) [] (fun j ih => ih ++ nthW R (s + j)) n

@[expose] noncomputable def blkOK (E : List Nat → List Nat → Bool) (R Q : List (List Nat))
    (g i : Nat) : Bool :=
  letLt (nthW Q i) && E (segC R (g * i) g) (nthW Q i)

@[expose] noncomputable def prodOK (E : List Nat → List Nat → Bool) (Q : List (List Nat)) (m : Nat) :
    Bool :=
  lenLe Q m && E (catW Q) [2]

end CFSG.KC.Fi24FiveK

end
