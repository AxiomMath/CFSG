module

public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KC.Misc.Clos

open CFSG.KC.Ord

@[expose] noncomputable def depthAt (PA D : Nat → Nat) (dmax k : Nat) : Bool :=
  andB (Nat.ble (D k) dmax)
    (Nat.rec (motive := fun _ => Bool) (Nat.beq (D (nat_lit 0)) (nat_lit 0))
      (fun _ _ => Nat.beq (D k) (Nat.succ (D (Nat.land (PA k) (nat_lit 16777215))))) k)

end CFSG.KC.Misc.Clos

end
