module

public import Certificates.Data.Kernel.HNLocalK

public section

namespace CFSG.KC.HNLocal

open CFSG.KC.Ord CFSG.KC.Loop

@[expose] noncomputable def unitV (a : Nat) : Nat :=
  Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 13) a)

@[expose] noncomputable def wordV (vm : Nat → Nat → Nat) (PC : Nat → Nat) (v e : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) v
    (fun i acc => strictN acc (fun a =>
      nIf(Nat.beq (Nat.land (Nat.shiftRight e i) (nat_lit 1)) (nat_lit 1), vm a (PC i), a)))

@[expose] noncomputable def elemV (vm : Nat → Nat → Nat) (PC : Nat → Nat) (nb U v e tg : Nat) :
    Bool :=
  Bool.rec (motive := fun _ => Bool)
    (letB (Nat.land (Nat.shiftRight tg (nat_lit 2)) (nat_lit 255)) (fun a =>
      andB (Nat.blt a (nat_lit 133))
        (notB (Nat.beq (wordV vm PC (wordV vm PC (unitV a) e nb) e nb) (unitV a)))))
    true
    (notB (Nat.beq (wordV vm PC v e nb) U))

@[expose] noncomputable def cenV (vm : Nat → Nat → Nat) (PC TG : Nat → Nat) (nb U : Nat) :
    Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun _ v e => elemV vm PC nb U v e (TG e))
    (fun _ ih k v e => bAnd(ih (Nat.succ k) v e,
      letB (vm v (PC k)) (fun v' => ih (Nat.succ k) v' (Nat.add e (Nat.shiftLeft (nat_lit 1) k)))))

@[expose] noncomputable def cenVAt (vm : Nat → Nat → Nat) (PC TG : Nat → Nat) (a0 m k n : Nat) :
    Bool :=
  letB (wordV vm PC (unitV a0) m k) (fun v => cenV vm PC TG (Nat.add k n) (unitV a0) n k v m)

end CFSG.KC.HNLocal

end
