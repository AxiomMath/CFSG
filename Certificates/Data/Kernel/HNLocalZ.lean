module

public import Certificates.Data.Kernel.HNLocalK

public section

namespace CFSG.KC.HNLocal

open CFSG.KC.Ord CFSG.KC.Loop

@[expose] noncomputable def evAt (EV i : Nat) : Nat :=
  Nat.land (Nat.shiftRight EV (Nat.mul (nat_lit 14) i)) (nat_lit 16383)

@[expose] noncomputable def evMem (EV e : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (Nat.beq e (evAt EV (nat_lit 3))) true
        (Nat.beq e (evAt EV (nat_lit 2))))
      true (Nat.beq e (evAt EV (nat_lit 1))))
    true (Nat.beq e (evAt EV (nat_lit 0)))

@[expose] noncomputable def zElemOK (vm : Nat → Nat → Nat) (PC : Nat → Nat) (RM Z EV M e tg : Nat) :
    Bool :=
  (fun kd k b => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) false
        (andB (Nat.blt k (nat_lit 14)) (andB (Nat.blt b (nat_lit 133))
          (letB (vm (rowL RM M b) (PC k)) fun x =>
            andB (notB (Nat.beq x (vm (rowL RM (PC k) b) M)))
              (notB (Nat.beq x (vm (vm (rowL RM Z b) (PC k)) M))))))
        (Nat.beq kd (nat_lit 1)))
      (evMem EV e)
      (Nat.beq kd (nat_lit 0)))
    (Nat.land tg (nat_lit 3)) (Nat.land (Nat.shiftRight tg (nat_lit 2)) (nat_lit 15))
    (Nat.shiftRight tg (nat_lit 6))

@[expose] noncomputable def zcen (mul vm : Nat → Nat → Nat) (PC TG : Nat → Nat) (RM Z EV : Nat) :
    Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun _ M e => zElemOK vm PC RM Z EV M e (TG e))
    (fun _ ih k M e => bAnd(ih (Nat.succ k) M e,
      letB (mul M (PC k)) (fun M' => ih (Nat.succ k) M' (Nat.add e (Nat.shiftLeft (nat_lit 1) k)))))

@[expose] noncomputable def zcenAt (mul vm : Nat → Nat → Nat) (PC TG : Nat → Nat) (ONE RM ez EV m k n : Nat) :
    Bool :=
  letB (nfPre mul PC ONE ez (nat_lit 14)) (fun Z =>
    letB (nfPre mul PC ONE m k) (fun M => zcen mul vm PC TG RM Z EV n k M m))

end CFSG.KC.HNLocal

end
