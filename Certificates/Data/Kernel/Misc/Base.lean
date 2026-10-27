module

public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KC.Misc

open CFSG.KC.Ord

@[expose] noncomputable def letN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def letLN (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def memN (x : Nat) (l : List Nat) : Bool :=
  CFSG.KC.LQT.P.letB x fun x =>
    List.rec (motive := fun _ => Bool) false (fun z _ ih => orB (Nat.beq x z) ih) l

@[expose] noncomputable def lenN (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def nodupN (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun z t ih => andB (notB (memN z t)) ih) l

@[expose] noncomputable def allLL (L : List (List Nat)) (f : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) L

@[expose] noncomputable def anyLL (L : List (List Nat)) (f : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => orB (f x) ih) L

@[expose] noncomputable def eqLN (a b : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false
      (fun y t _ => andB (Nat.beq x y) (ih t)) b) a b

end CFSG.KC.Misc

end
