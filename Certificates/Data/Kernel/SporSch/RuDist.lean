module

public import Certificates.Data.Kernel.SporSch.RuImg

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def distNL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x xs ih => Bool.rec (motive := fun _ => Nat) (Nat.succ ih) ih (memNL x xs)) l

end CFSG.KS.SporSch

end
