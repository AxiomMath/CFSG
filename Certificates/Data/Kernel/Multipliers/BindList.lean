module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.BindList

open CFSG.KC.Enum

@[expose] noncomputable def bindListK (w m P : Nat) (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih k => bAnd(Nat.beq x (pg w m P k), strictB (Nat.succ k) ih)) l

end CFSG.KC.BindList

end
