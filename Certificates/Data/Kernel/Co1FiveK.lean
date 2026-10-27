module

public import Certificates.Data.Kernel.SporSch.Co1MatW
public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import Certificates.Data.Kernel.Co1End
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Co1FiveK

open CFSG.KC.Enum CFSG.KS.SporSch.M24

@[expose] noncomputable def pwK (M e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idM (fun _ acc => strictN acc fun a => CFSG.KC.Co1B.mulWK a M) e

@[expose] noncomputable def a0K (D : Nat → Nat) (k : Nat) : Nat :=
  CFSG.KC.Co1B.mulWK (pwK (D 0) (Nat.mod k 5))
    (CFSG.KC.Co1B.mulWK (pwK (D 1) (Nat.mod (Nat.div k 5) 5)) (pwK (D 2) (Nat.div k 25)))

end CFSG.KC.Co1FiveK

end
