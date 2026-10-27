module

public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Spor.Mathieu

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu

@[expose] noncomputable def wordPKFrom (n w : Nat) (G GI : Nat → Nat) (v : List (Nat × Bool))
    (P : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) P
    (fun l _ acc => strictN acc (fun a =>
      pcomp n w (mask w) (Bool.rec (GI l.1) (G l.1) l.2) a)) v

@[expose] noncomputable def takeL (k : Nat) (v : List (Nat × Bool)) : List (Nat × Bool) :=
  List.rec (motive := fun _ => Nat → List (Nat × Bool)) (fun _ => [])
    (fun x _ ih k => Nat.rec (motive := fun _ => List (Nat × Bool)) [] (fun k' _ => x :: ih k') k)
    v k

@[expose] noncomputable def dropL (k : Nat) (v : List (Nat × Bool)) : List (Nat × Bool) :=
  List.rec (motive := fun _ => Nat → List (Nat × Bool)) (fun _ => [])
    (fun x xs ih k => Nat.rec (motive := fun _ => List (Nat × Bool)) (x :: xs) (fun k' _ => ih k') k)
    v k

@[expose] noncomputable def wAt (W : List (List (Nat × Bool))) (r : Nat) : List (Nat × Bool) :=
  List.rec (motive := fun _ => Nat → List (Nat × Bool)) (fun _ => [])
    (fun x _ ih r => Nat.rec (motive := fun _ => List (Nat × Bool)) x (fun r' _ => ih r') r) W r

@[expose] noncomputable def wordEqL (v : List (Nat × Bool)) : List (Nat × Bool) → Bool :=
  List.rec (motive := fun _ => List (Nat × Bool) → Bool)
    (fun u => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) u)
    (fun x _ ih u => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => bAnd(Nat.beq x.1 y.1, bAnd(Bool.rec (Bool.not y.2) y.2 x.2, ih ys))) u) v

@[expose] noncomputable def lenL (v : List (Nat × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) v

end CFSG.KS.SporSch

end
