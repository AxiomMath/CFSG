module

public import Certificates.Data.Kernel.Cert690.SqPass
public import Certificates.Data.Kernel.Cert690.Pgl

public section

namespace CFSG.KC.C690

open CFSG.KC.Enum

@[expose] noncomputable def invOKL (n : Nat) (E : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x _ ih => andK (Nat.beq (mulF x (invGo x n x)) oneF) ih) E

@[expose] noncomputable def eqK (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false b) b a

@[expose] noncomputable def invBitsL (M : Nat) (E : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih j => strictB j fun j => andK (eqK (isInvF x) (bitK M j)) (ih (Nat.succ j))) E

end CFSG.KC.C690

end
