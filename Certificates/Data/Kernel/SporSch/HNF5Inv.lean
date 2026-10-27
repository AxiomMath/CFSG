module

public import Certificates.Data.Kernel.SporSch.HNF5

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum

@[expose] noncomputable def vecChain5 (MT : Nat → Nat) (E : Nat) (lt : Nat → Nat) (w : List Nat) :
    Bool :=
  allN w.length (fun t => Nat.beq (slice5 MT E (Nat.succ t))
    (vm5 (slice5 MT (lt (w.getD (Nat.sub (Nat.sub w.length 1) t) 0))) (slice5 MT E t)))

end CFSG.KS.SporSch

end
