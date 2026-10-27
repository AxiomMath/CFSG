module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.PtOrb

open CFSG.KC.Enum (strictN strictB)

@[expose] noncomputable def bitP (s x : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight s x) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def allF (m : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => bAnd(f i, ih)) m

@[expose] noncomputable def imgF (f : Nat → Nat) (s n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x acc => nIf(bitP s x, Nat.lor acc (Nat.shiftLeft (nat_lit 1) (f x)), acc)) n

@[expose] noncomputable def roundF (f : Nat → Nat → Nat) (k n s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) s (fun j acc => Nat.lor acc (imgF (f j) s n)) k

@[expose] noncomputable def closeF (f : Nat → Nat → Nat) (k n r s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun _ ih s => strictN (roundF f k n s) ih) r s

@[expose] noncomputable def closedF (f : Nat → Nat → Nat) (k n s : Nat) : Bool :=
  allF k fun j => Nat.beq (Nat.lor (imgF (f j) s n) s) s

@[expose] noncomputable def orbClosed (f : Nat → Nat → Nat) (k n r x : Nat) : Bool :=
  strictB (closeF f k n r (Nat.shiftLeft (nat_lit 1) x)) (closedF f k n)

@[expose] noncomputable def bitsIs (S n : Nat) (t : Nat → Bool) : Bool :=
  strictB S fun s => allF n fun y => bIf(bitP s y, t y, Bool.rec (motive := fun _ => Bool) true false (t y))

@[expose] noncomputable def popF (s n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun y acc => Nat.add acc (nIf(bitP s y, nat_lit 1, nat_lit 0))) n

@[expose] noncomputable def popIs (S n c : Nat) : Bool :=
  strictB S fun s => Nat.beq (popF s n) c

end CFSG.KC.PtOrb

end
