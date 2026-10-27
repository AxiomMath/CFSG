module

public import CFSG.Certificates.Kernel.Common.Lce

public section

namespace CFSG.KC.LceSeg

open CFSG.KC

@[expose] noncomputable def strictL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k 0) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def seg (f : Nat → Nat) (n : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih k => List.cons (f k) (strictL (Nat.succ k) ih)) n

@[expose] noncomputable def slOK (F : List Nat → Nat → Nat) (f lo acc : Nat → Nat) (i : Nat) :
    Bool :=
  andB (Nat.ble (lo i) (lo (Nat.succ i)))
    (Nat.beq (F (seg f (Nat.sub (lo (Nat.succ i)) (lo i)) (lo i)) (acc i)) (acc (Nat.succ i)))

end CFSG.KC.LceSeg

end
