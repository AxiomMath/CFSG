module

public import Certificates.Data.Kernel.MinusQuandle

public section

namespace CFSG.KD.MinusSecondKind

open CFSG.KD.MinusQuandle

@[expose] def bOr (x y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) y true x

@[expose] def bAnd (x y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false y x

@[expose] def bNot (x : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false x

@[expose] def ln (r x : ℕ) : ℕ := Nat.land (Nat.shiftRight r (Nat.mul 7 x)) 127

@[expose] def invOK (R : ℕ → ℕ) : Bool :=
  allF 65 fun a => force (R a) fun r => allF 65 fun x => Nat.beq (ln r (ln r (x))) x

@[expose] def quandleRow (R : ℕ → ℕ) (ra b : ℕ) : Bool :=
  force (R b) fun rb => force (R (ln ra b)) fun rc =>
    allF 65 fun x => Nat.beq (ln ra (ln rb (ln ra x))) (ln rc x)

@[expose] def quandleOK (R : ℕ → ℕ) : Bool :=
  allF 65 fun a => force (R a) fun ra => allF 65 fun b => quandleRow R ra b

@[expose] def keyOf (r : ℕ) : ℕ :=
  Nat.add (ln r 0) (Nat.add (Nat.mul 128 (ln r 1)) (Nat.mul 16384 (ln r 29)))

@[expose] def baseOK (R : ℕ → ℕ) : Bool :=
  allF 65 fun a => force (keyOf (R a)) fun ka =>
    allF 65 fun b => bOr (Nat.beq a b) (bNot (Nat.beq ka (keyOf (R b))))

@[expose] def skT (R : ℕ → ℕ) (ri rk i k j : ℕ) : Bool :=
  bOr (Nat.beq (ln ri j) j) (bOr (Nat.beq (ln rk j) j) (force (ln ri (ln rk j)) fun m =>
    bOr (bNot (Nat.beq (ln (R m) j) j)) (bOr (Nat.beq m j) (force (R j) fun rj =>
      bAnd (Nat.beq (ln ri j) (ln rj i)) (Nat.beq (ln rk j) (ln rj k))))))

@[expose] def skOK (R : ℕ → ℕ) : Bool :=
  allF 65 fun i => force (R i) fun ri => allF 65 fun k =>
    bOr (Nat.beq i k) (bOr (bNot (Nat.beq (ln ri k) k)) (force (R k) fun rk =>
      allF 65 fun j => skT R ri rk i k j))

end CFSG.KD.MinusSecondKind
