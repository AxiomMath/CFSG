module

public import Certificates.Data.Kernel.Misc.BfsK

public section

namespace CFSG.KD.BfsKW

open CFSG.KD.Sp62 (buildG stepG)
open CFSG.KD.BfsK

@[expose] noncomputable def M32 : Nat := 4294967295

@[expose] noncomputable def recFW (R : Nat → Nat) (o f t : Nat) : Nat :=
  Nat.land (Nat.shiftRight (R (Nat.add o t)) (Nat.add 64 (Nat.mul 32 f))) M32

@[expose] noncomputable def recCW (R : Nat → Nat) (o k i : Nat) : Nat :=
  recFW R o (Nat.add 4 (Nat.mod i k)) (Nat.div i k)

@[expose] noncomputable def recPOSW (R : Nat → Nat) (o k i : Nat) : Nat :=
  recFW R o (Nat.add (Nat.add 4 k) (Nat.mod i k)) (Nat.div i k)

@[expose] noncomputable def tableKW (R : Nat → Nat) (st : Nat → Nat → Nat) (o n k hiB hiS hiT : Nat) :
    Bool :=
  buildG st (recX R o) (recFW R o 0) (recFW R o 1) n k hiB &&
    stepG st (recX R o) (recFW R o 0) (recFW R o 1) (recCW R o k) (recPOSW R o k) n k hiS &&
    CFSG.KD.G2Three.sortK (recX R o) (recFW R o 2) (recFW R o 3) n hiT

end CFSG.KD.BfsKW

end
