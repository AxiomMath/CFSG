module

public import Certificates.Data.Kernel.ThCensus.Words

public section

namespace CFSG.KC.ThCensus

open CFSG.KC.Th CFSG.KC.Th.BigS

@[expose] noncomputable def wordLetOK (q : Nat) (n : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih J => andB (Nat.blt (Nat.land J (nat_lit 3)) q) (ih (Nat.shiftRight J (nat_lit 2)))) n

@[expose] noncomputable def ord3OK (RB : Nat → Nat) (c rm ONE r : Nat) : Bool :=
  andB (Nat.beq (mulB c rm (mulB c rm (RB r) (RB r)) (RB r)) ONE)
    (notB (Nat.beq (mulB c rm (RB r) ONE) ONE))

end CFSG.KC.ThCensus

end
