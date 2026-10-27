module

public import Certificates.Data.Kernel.Sp62Pk

public section

namespace CFSG.KD.BfsK

open CFSG.KD.Sp62

@[expose] noncomputable def M64 : Nat := 18446744073709551615

@[expose] noncomputable def recX (R : Nat → Nat) (o t : Nat) : Nat := Nat.land (R (Nat.add o t)) M64

@[expose] noncomputable def recF (R : Nat → Nat) (o f t : Nat) : Nat :=
  Nat.land (Nat.shiftRight (R (Nat.add o t)) (Nat.add 64 (Nat.mul 16 f))) 65535

@[expose] noncomputable def recC (R : Nat → Nat) (o k i : Nat) : Nat :=
  recF R o (Nat.add 4 (Nat.mod i k)) (Nat.div i k)

@[expose] noncomputable def recPOS (R : Nat → Nat) (o k i : Nat) : Nat :=
  recF R o (Nat.add (Nat.add 4 k) (Nat.mod i k)) (Nat.div i k)

@[expose] noncomputable def tableKk (R : Nat → Nat) (st : Nat → Nat → Nat) (o n k hiB hiS hiT : Nat) :
    Bool :=
  buildG st (recX R o) (recF R o 0) (recF R o 1) n k hiB &&
    stepG st (recX R o) (recF R o 0) (recF R o 1) (recC R o k) (recPOS R o k) n k hiS &&
    CFSG.KD.G2Three.sortK (recX R o) (recF R o 2) (recF R o 3) n hiT

end CFSG.KD.BfsK

end
