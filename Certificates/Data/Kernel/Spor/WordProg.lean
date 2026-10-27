module

public import CFSG.Certificates.Kernel.Orders.Cert

public section

namespace CFSG.KC.Ord

@[expose] noncomputable def strictL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def letC (c : Nat) : Nat × Bool :=
  Prod.mk (Nat.shiftRight c (nat_lit 1)) (Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def hdN (ONE : Nat) (st : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) ONE (fun x _ _ => x) st

@[expose] noncomputable def tlN (st : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun _ xs _ => xs) st

@[expose] noncomputable def stepV (RB : Nat → Nat) (L : Nat) (RS : Nat → Nat)
    (mul : Nat → Nat → Nat) (ONE ins : Nat) (st : List Nat) : List Nat :=
  (fun t a => Bool.rec (motive := fun _ => List Nat)
      (Bool.rec (motive := fun _ => List Nat)
        (Bool.rec (motive := fun _ => List Nat)
          (strictL (powR mul ONE (hdN ONE st) a) (fun v => List.cons v (tlN st)))
          (strictL (mul (hdN ONE (tlN st)) (hdN ONE st)) (fun v => List.cons v (tlN (tlN st))))
          (Nat.beq t (nat_lit 2)))
        (strictL (RS a) (fun v => List.cons v st))
        (Nat.beq t (nat_lit 1)))
      (strictL (letM RB L (letC a)) (fun v => List.cons v st))
      (Nat.beq t (nat_lit 0)))
    (Nat.land ins (nat_lit 3)) (Nat.shiftRight ins (nat_lit 2))

@[expose] noncomputable def progVal (RB : Nat → Nat) (L : Nat) (RS : Nat → Nat)
    (mul : Nat → Nat → Nat) (ONE : Nat) (P : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun st => st)
    (fun ins _ ih st => ih (stepV RB L RS mul ONE ins st)) P

@[expose] noncomputable def progTop (RB : Nat → Nat) (L : Nat) (RS : Nat → Nat)
    (mul : Nat → Nat → Nat) (ONE : Nat) (P : List Nat) : Nat :=
  hdN ONE (progVal RB L RS mul ONE P List.nil)

@[expose] noncomputable def progOK (RB : Nat → Nat) (L : Nat) (RS : Nat → Nat)
    (mul : Nat → Nat → Nat) (ONE : Nat) (P : List Nat) (T : Nat) : Bool :=
  Nat.beq (progTop RB L RS mul ONE P) T

@[expose] noncomputable def relProgsRangeOK (RB : Nat → Nat) (L : Nat) (RS : Nat → Nat)
    (mul : Nat → Nat → Nat) (ONE : Nat) (PR : Nat → List Nat) (lo n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB ih (progOK RB L RS mul ONE (PR (Nat.add lo i)) ONE)) n

@[expose] noncomputable def stateProgsRangeOK (RB : Nat → Nat) (L : Nat) (RS : Nat → Nat)
    (mul : Nat → Nat → Nat) (ONE : Nat) (PS : Nat → List Nat) (lo n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB ih (progOK RB L RS mul ONE (PS (Nat.add lo i)) (RS (Nat.add lo i)))) n

end CFSG.KC.Ord

end
