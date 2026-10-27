module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.Misc.F7

open CFSG.KC.Loop

@[expose] noncomputable def andB (a b : Bool) : Bool := bAnd(a, b)

@[expose] noncomputable def ifB (c t e : Bool) : Bool := bIf(c, t, e)

@[expose] noncomputable def ifN (c : Bool) (t e : Nat) : Nat := nIf(c, t, e)

@[expose] noncomputable def notB (a : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false a

@[expose] noncomputable def sumN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => Nat.add acc (f k)) n

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB (f k) ih) n

@[expose] noncomputable def rowMask : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1440)) (nat_lit 1)

@[expose] noncomputable def m8 : Nat :=
  sumN (nat_lit 45) fun j => Nat.shiftLeft (nat_lit 255) (Nat.mul (nat_lit 32) j)

@[expose] noncomputable def red7 (v : Nat) : Nat :=
  Nat.sub v (Nat.mul (nat_lit 7)
    (Nat.land (Nat.shiftRight (Nat.mul v (nat_lit 4682)) (nat_lit 15)) m8))

@[expose] noncomputable def row (A i : Nat) : Nat := fld(A, Nat.mul (nat_lit 1440) i, rowMask)

@[expose] noncomputable def lane (r j : Nat) : Nat := fld(r, Nat.mul (nat_lit 32) j, nat_lit 4294967295)

@[expose] noncomputable def rowMul (r B : Nat) : Nat :=
  red7 (sumN (nat_lit 45) fun k => Nat.mul (lane r k) (row B k))

@[expose] noncomputable def rowsMul (m A B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN (rowMul (row A i) B) fun r =>
      Nat.add acc (Nat.shiftLeft r (Nat.mul (nat_lit 1440) i))) m

@[expose] noncomputable def mmul (A B : Nat) : Nat := rowsMul (nat_lit 45) A B

@[expose] noncomputable def idM : Nat :=
  sumN (nat_lit 45) fun i => Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 1472) i)

@[expose] noncomputable def powM (A e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idM (fun _ acc => strictN (mmul acc A) fun x => x) e

@[expose] noncomputable def widenR (m c : Nat) : Nat :=
  sumN m fun i => sumN (nat_lit 45) fun j => Nat.shiftLeft
    (Nat.mod (fld(c, Nat.mul (nat_lit 3) (Nat.add (Nat.mul (nat_lit 45) i) j), nat_lit 7))
      (nat_lit 7))
    (Nat.mul (nat_lit 32) (Nat.add (Nat.mul (nat_lit 45) i) j))

@[expose] noncomputable def widen (c : Nat) : Nat := widenR (nat_lit 45) c

@[expose] noncomputable def imgS (S G : Nat) : Nat := rowsMul (nat_lit 8) S G

@[expose] noncomputable def nthF (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih j => Nat.rec (motive := fun _ => Nat) x (fun j' _ => ih j') j) l i

@[expose] noncomputable def redRow (x V : Nat) (piv : List Nat) : Nat :=
  red7 (Nat.add x (sumN (nat_lit 8) fun c =>
    Nat.mul (Nat.sub (nat_lit 7) (lane x (nthF piv c))) (row V c)))

@[expose] noncomputable def inSpan (U V : Nat) (piv : List Nat) : Bool :=
  allN (nat_lit 8) fun i => Nat.beq (redRow (row U i) V piv) (nat_lit 0)

@[expose] noncomputable def pivOK (V : Nat) (piv : List Nat) : Bool :=
  allN (nat_lit 8) fun c => andB (Nat.blt (nthF piv c) (nat_lit 45))
    (allN (nat_lit 8) fun c' => Nat.beq (lane (row V c') (nthF piv c))
      (ifN (Nat.beq c' c) (nat_lit 1) (nat_lit 0)))

end CFSG.KC.Misc.F7

end
