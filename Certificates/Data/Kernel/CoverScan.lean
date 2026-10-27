module

public import Certificates.Data.Kernel.L34K

public section

namespace CFSG.KC.CoverScan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def coverK (n w M : Nat) (ON : Nat → Nat) (OT : Nat → Nat → Nat)
    (e v x : Nat) : Bool :=
  orB (Nat.beq x e) (orB (notB (invPt n w x))
    (strictB (Nat.shiftRight v (nat_lit 12)) fun o => strictB (Nat.land v (nat_lit 4095)) fun j =>
      andB (Nat.blt o M) (andB (Nat.blt j (ON o)) (Nat.beq (OT o j) x))))

end CFSG.KC.CoverScan

end
