module

public import Certificates.Data.Kernel.Sp62Pk

public section

namespace CFSG.KD.Sp6Two

open CFSG.KD.Sp62

@[expose] noncomputable def recCk (R : Nat → Nat) (o k i : Nat) : Nat :=
  recF R o (Nat.add 4 (Nat.mod i k)) (Nat.div i k)

@[expose] noncomputable def recPOSk (R : Nat → Nat) (o k i : Nat) : Nat :=
  recF R o (Nat.add (Nat.add 4 k) (Nat.mod i k)) (Nat.div i k)

@[expose] noncomputable def tableKG (R : Nat → Nat) (st : Nat → Nat → Nat)
    (o n k hiB hiS hiT : Nat) : Bool :=
  buildG st (recX R o) (recF R o 0) (recF R o 1) n k hiB &&
    stepG st (recX R o) (recF R o 0) (recF R o 1) (recCk R o k) (recPOSk R o k) n k hiS &&
    CFSG.KD.G2Three.sortK (recX R o) (recF R o 2) (recF R o 3) n hiT

end CFSG.KD.Sp6Two

end
