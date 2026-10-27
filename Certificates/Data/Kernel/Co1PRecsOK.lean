module

public import Certificates.Data.Kernel.TreeK

public section

namespace CFSG.KC.Co1P

open CFSG.KLie.CT

@[expose] noncomputable def recsOKK (ng : Nat) : List (Nat × Nat) → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun r _ ih h n => andB (andB (Nat.ble h r.1) (andB (Nat.blt r.1 n) (Nat.blt r.2 ng)))
      (ih r.1 (Nat.succ n)))

@[expose] noncomputable def recAtK (ng : Nat) (R : Nat → Nat) (i : Nat) : Bool :=
  andB (orB (Nat.beq i 0) (Nat.ble (Nat.div (R (Nat.sub i 1)) 8) (Nat.div (R i) 8)))
    (andB (Nat.ble (Nat.div (R i) 8) i) (Nat.blt (Nat.mod (R i) 8) ng))

end CFSG.KC.Co1P

end
