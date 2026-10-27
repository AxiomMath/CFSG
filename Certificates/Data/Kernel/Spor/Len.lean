module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.Len

open CFSG.KC.Enum

@[expose] noncomputable def lenFrom (cs : List Char) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun k => k)
    (fun _ _ ih k => strictN (Nat.succ k) ih) cs

@[expose] noncomputable def lenK (cs : List Char) : Nat := lenFrom cs (nat_lit 0)

end CFSG.KS.Len

end
