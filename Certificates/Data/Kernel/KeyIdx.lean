module

public import Certificates.Data.Kernel.PGrp

public section

namespace CFSG.KC.PGrp

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def keyIdx (n w : Nat) (R : Nat → Nat) (k : Nat) : Nat :=
  pg w (mask w) (R (Nat.div k n)) (Nat.mod k n)

@[expose] noncomputable def mulIdx (n w : Nat) (ps : List Nat) (R : Nat → Nat) (P Q : Nat) : Nat :=
  keyIdx n w R (keyCK n w ps P Q)

end CFSG.KC.PGrp

end
