module

public import Certificates.Data.Kernel.Misc.Base

public section

namespace CFSG.KC.GL62

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc

@[expose] noncomputable def W64 : Nat := nat_lit 18446744073709551615

@[expose] noncomputable def R6 : Nat := nat_lit 1090785345

@[expose] noncomputable def lrep (N : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul (nat_lit 64) N)) 1) W64

@[expose] noncomputable def mulL (Rl Fl A B : Nat) : Nat :=
  letN A fun A => letN B fun B =>
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => Nat.xor acc (Nat.land
    (Nat.mul (Nat.land (Nat.shiftRight A k) Rl) (nat_lit 63))
    (Nat.mul (Nat.land (Nat.shiftRight B (Nat.mul (nat_lit 6) k)) Fl) R6))) (nat_lit 6)

@[expose] noncomputable def cmulK (a b : Nat) : Nat := mulL R6 (nat_lit 63) b a

@[expose] noncomputable def packL (xs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor x (Nat.shiftLeft ih (nat_lit 64))) xs

@[expose] noncomputable def laneK (P k : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul (nat_lit 64) k)) W64

@[expose] noncomputable def nzL (N L Z : Nat) : Nat :=
  Nat.land (Nat.shiftRight (Nat.mul (Nat.land (Nat.shiftRight
      (Nat.add Z (Nat.mul (nat_lit 68719476735) L)) (nat_lit 36)) L) L)
    (Nat.mul (nat_lit 64) (Nat.sub N 1))) W64

@[expose] noncomputable def geL (L Y m : Nat) : Bool :=
  letB (Nat.shiftLeft L (nat_lit 36)) fun G =>
    Nat.beq (Nat.land (Nat.sub (Nat.lor Y G) (Nat.mul m L)) G) G

@[expose] noncomputable def LLmask : Nat := nat_lit 233016

@[expose] noncomputable def ULmask : Nat := nat_lit 29127

@[expose] noncomputable def blkK (c : Nat) : Bool :=
  letB (Nat.land c (nat_lit 262143)) fun lo => letB (Nat.shiftRight c (nat_lit 18)) fun hi =>
  letB (Nat.land hi ULmask) fun ur =>
  andB (Nat.blt c (nat_lit 68719476736)) (andB (Nat.beq (Nat.land lo LLmask) 0)
    (andB (Nat.beq (Nat.land (Nat.shiftRight hi (nat_lit 3)) ULmask) lo)
      (orB (Nat.beq ur 0) (Nat.beq ur lo))))

end CFSG.KC.GL62

end
