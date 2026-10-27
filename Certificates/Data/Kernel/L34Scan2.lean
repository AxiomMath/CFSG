module

public import Certificates.Data.Kernel.L34K

public section

namespace CFSG.KC.L34Scan2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.KLie.CT (notB)

@[expose] noncomputable def ppowK (x k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn (nat_lit 42) (nat_lit 6))
    (fun _ y => pcomp (nat_lit 42) (nat_lit 6) (mask 6) y x) k

@[expose] noncomputable def memL (N : Nat) (T : Nat → Nat) (x : Nat) : Bool :=
  notB (allN N fun q => notB (Nat.beq (T q) x))

end CFSG.KC.L34Scan2

end
