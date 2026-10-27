module

public import Certificates.Data.Kernel.Sp62Pk

public section

namespace CFSG.KD.Sp6Cls

open CFSG.KD.Sp62

@[expose] noncomputable def andC (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def orC (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def notC (a : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false a

@[expose] noncomputable def allNC (m : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => andC (f i) acc) m

@[expose] noncomputable def anyNC (m : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i acc => orC (f i) acc) m

@[expose] noncomputable def letC (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def outO (RO : Nat → Nat) (oo no x : Nat) : Bool :=
  allNC no fun s => notC (Nat.beq (recX RO oo s) x)

@[expose] noncomputable def c7K (R : Nat → Nat) (o n : Nat) (RO : Nat → Nat) (oo no : Nat) : Bool :=
  allNC n fun t => letC (recX R o t) fun x =>
    orC (notC (Nat.beq (MULF x x) ONE)) (orC (Nat.beq x ONE) (outO RO oo no x))

@[expose] noncomputable def commG (G : Nat → Nat) (k x : Nat) : Bool :=
  allNC k fun s => Nat.beq (MULF x (G s)) (MULF (G s) x)

@[expose] noncomputable def sylK (R : Nat → Nat) (o n : Nat) (G : Nat → Nat) (k T : Nat)
    (RO : Nat → Nat) (oo no : Nat) : Bool :=
  letC T fun T =>
    andC (allNC k fun s => Nat.beq (MULF (G s) T) (MULF T (G s)))
      (andC (anyNC n fun t => Nat.beq (recX R o t) T)
        (allNC n fun t => letC (recX R o t) fun x =>
          orC (notC (commG G k x)) (orC (notC (Nat.beq (MULF x x) ONE))
            (orC (Nat.beq x ONE) (orC (outO RO oo no x) (Nat.beq x T))))))

end CFSG.KD.Sp6Cls
