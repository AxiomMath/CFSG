module

public import Certificates.Data.Kernel.PCent

public section

namespace CFSG.KC.O8Sq

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def cntCommK (n w x : Nat) : List (Nat × Nat × Nat × Nat) → Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r _ ih => Bool.rec (motive := fun _ => Nat) ih (Nat.succ ih)
      (Prod.rec (motive := fun _ => Bool)
        (fun v _ => Nat.beq (pcomp n w (mask w) v x) (pcomp n w (mask w) x v)) r))

end CFSG.KC.O8Sq

end
