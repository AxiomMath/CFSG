module

public import Certificates.Data.Kernel.LocalQT.Six

public section

namespace CFSG.KC.LQT.X6

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def factK (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 1 (fun k f => Nat.mul f (Nat.succ k)) k

@[expose] noncomputable def pickK (used d : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk 6 d)
    (fun v acc => Bool.rec (motive := fun _ => Nat × Nat)
      (Bool.rec (motive := fun _ => Nat × Nat)
        (Bool.rec (motive := fun _ => Nat × Nat) (Prod.mk acc.1 (Nat.sub acc.2 1)) (Prod.mk v 0)
          (Nat.beq acc.2 0))
        acc (Nat.blt 0 (Nat.land used (Nat.shiftLeft 1 v))))
      acc (Nat.blt acc.1 6)) 6).1

@[expose] noncomputable def unrank6 (r : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk 0 0)
    (fun i acc => (fun v => Prod.mk (Nat.add acc.1 (Nat.shiftLeft v (Nat.mul 5 i)))
        (Nat.lor acc.2 (Nat.shiftLeft 1 v)))
      (pickK acc.2 (Nat.mod (Nat.div r (factK (Nat.sub 5 i))) (Nat.sub 6 i)))) 6).1

@[expose] noncomputable def rankOK : Bool := allP 6 fun x => Nat.beq (unrank6 (rank6 x)) x

end CFSG.KC.LQT.X6

end
