module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.Co3Tw

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def ord3K (p : Nat) : Bool :=
  Nat.beq (pcomp 276 9 (mask 9) p (pcomp 276 9 (mask 9) p p)) (pidn 276 9) && !Nat.beq p (pidn 276 9)

@[expose] noncomputable def cntO3 (N : Nat) (T : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i ih => Nat.add ih (Bool.rec 0 1 (ord3K (T i)))) N

end CFSG.KC.Co3Tw

end
