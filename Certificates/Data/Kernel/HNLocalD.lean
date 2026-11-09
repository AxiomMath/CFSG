module

public import Certificates.Data.Kernel.HNLocalV

public section

namespace CFSG.KC.HNLocal

open CFSG.KC.Ord CFSG.KC.Loop

@[expose] noncomputable def memND (e : Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun d _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq e d))

@[expose] noncomputable def elemVD (vm : Nat → Nat → Nat) (PC : Nat → Nat) (D : List Nat)
    (nb U v e tg : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (elemV vm PC nb U v e tg) true (memND e D)

@[expose] noncomputable def cenVD (vm : Nat → Nat → Nat) (PC TG : Nat → Nat) (D : List Nat)
    (nb U : Nat) : Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun _ v e => elemVD vm PC D nb U v e (TG e))
    (fun _ ih k v e => bAnd(ih (Nat.succ k) v e,
      letB (vm v (PC k)) (fun v' => ih (Nat.succ k) v' (Nat.add e (Nat.shiftLeft (nat_lit 1) k)))))

@[expose] noncomputable def cenVDAt (vm : Nat → Nat → Nat) (PC TG : Nat → Nat) (D : List Nat)
    (a0 m k n : Nat) : Bool :=
  letB (wordV vm PC (unitV a0) m k) (fun v => cenVD vm PC TG D (Nat.add k n) (unitV a0) n k v m)

@[expose] noncomputable def cenDL (mul vm : Nat → Nat → Nat) (PC RP TG : Nat → Nat)
    (np ONE RM k : Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun d _ ih => bAnd(Nat.blt d (Nat.shiftLeft (nat_lit 1) k),
      bAnd(cenAt mul vm PC RP TG np ONE RM d k (nat_lit 0), ih)))

end CFSG.KC.HNLocal

end
