module

public import Certificates.Data.Kernel.GMS78RuS

public section

namespace CFSG.KC.GMS

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def sIdx (C : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.lor (Nat.shiftLeft (Nat.succ i) (Nat.mul 9 x)) (ih (Nat.succ i))) C 0

@[expose] noncomputable def sClosed (m : Nat → Nat → Nat) (C : List Nat) : Bool :=
  neStrictB (sIdx C) fun IDX =>
    neAllL (fun p => neAllL (fun q => notB (Nat.beq (fget IDX (m p q) 9) 0)) C) C

@[expose] noncomputable def kClo17 (m : Nat → Nat → Nat) (u k : Nat) : Bool :=
  orB (notB (kNeedZ u k)) (sClosed m (sFilter 8192 fun p => Nat.beq (m p u) (m u p)))

end CFSG.KC.GMS

end
