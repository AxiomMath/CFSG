module

public import Certificates.Data.Kernel.SporSch.J4SCols

public section

namespace CFSG.KS.SporSch.C11

open CFSG.KC.Enum

@[expose] noncomputable def powKF (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => pidK)
    (fun _ ih P m => nIf(Nat.beq m (nat_lit 0), pidK, strictN (compK P P) (fun PP =>
      nIf(Nat.beq (Nat.mod m (nat_lit 2)) (nat_lit 1), compK P (ih PP (Nat.div m (nat_lit 2))),
        ih PP (Nat.div m (nat_lit 2)))))) f

end CFSG.KS.SporSch.C11

end
