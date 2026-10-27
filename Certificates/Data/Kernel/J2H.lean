module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.J2H

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def commAllK (k : Nat) (G : Nat → Nat) (X : Nat) : Bool :=
  allN k (fun j => Nat.beq (pcomp 315 9 (mask 9) X (G j)) (pcomp 315 9 (mask 9) (G j) X))

end CFSG.KC.J2H
