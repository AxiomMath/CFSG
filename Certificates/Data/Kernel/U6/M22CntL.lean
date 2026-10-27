module

public import Certificates.Data.Kernel.U6.M22Cnt

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2

@[expose] noncomputable def commA (r : Nat) (ap : Nat → Nat) : Bool :=
  allN (nat_lit 22) fun i => Nat.beq (ap (ap5 r i)) (ap5 r (ap i))

@[expose] noncomputable def sqA (ap : Nat → Nat) : Bool :=
  allN (nat_lit 22) fun i => Nat.beq (ap (ap i)) i

@[expose] noncomputable def isIdA (ap : Nat → Nat) : Bool :=
  allN (nat_lit 22) fun i => Nat.beq (ap i) i

@[expose] noncomputable def sqMulA (s : Nat) (ap : Nat → Nat) : Bool :=
  allN (nat_lit 22) fun i => Nat.beq (ap (ap5 s (ap (ap5 s i)))) i

@[expose] noncomputable def missOutA (r : Nat) (L : List Nat) (ap : Nat → Nat) (x : Nat) : Bool :=
  andB (sqA ap) (andB (commA r ap) (andB (notB (isIdA ap))
    (orB (notB (memK L (keyK x))) (notB (memK L (keyK (pc22 x r)))))))

@[expose] noncomputable def missInA (r : Nat) (L : List Nat) (ap : Nat → Nat) (x : Nat) : Bool :=
  andB (sqA ap) (andB (commA r ap) (andB (notB (isIdA ap))
    (andB (notB (Nat.beq x r)) (notB (memK L (keyK x))))))

@[expose] noncomputable def cntVecA (R8 R0 RY : Nat) (L8 L0 LY : List Nat) (ap : Nat → Nat)
    (x : Nat) : Nat :=
  Nat.add (ind (orB (missOutA R8 L8 ap x) (orB (missOutA R0 L0 ap x) (missInA RY LY ap x)))
      (nat_lit 0))
    (Nat.add (ind (sqMulA R8 ap) (nat_lit 1))
      (Nat.add (ind (andB (sqA ap) (notB (isIdA ap))) (nat_lit 2))
        (Nat.add (ind (commA R8 ap) (nat_lit 3))
          (Nat.add (ind (commA R0 ap) (nat_lit 4)) (ind (commA RY ap) (nat_lit 5))))))

@[expose] noncomputable def apF (p q i : Nat) : Nat :=
  nIf(Nat.blt i (nat_lit 22), fld(p, Nat.mul (nat_lit 5) fld(q, Nat.mul (nat_lit 5) i, nat_lit 31),
    nat_lit 31), nat_lit 0)

@[expose] noncomputable def ap3 (y d t i : Nat) : Nat :=
  nIf(Nat.blt i (nat_lit 22), apF y d fld(t, Nat.mul (nat_lit 5) i, nat_lit 31), nat_lit 0)

@[expose] noncomputable def chunkL (R8 R0 RY : Nat) (L8 L0 LY : List Nat) (TR : Nat → Nat)
    (o a : Nat) : Nat :=
  strictN (TR (Nat.add (fget o (nat_lit 0) (nat_lit 32)) a)) fun x0 =>
  sumN (nat_lit 21) fun b => strictN (pc22 x0 (TR (Nat.add (fget o (nat_lit 1) (nat_lit 32)) b)))
    fun x1 =>
  sumN (nat_lit 20) fun c => strictN (pc22 x1 (TR (Nat.add (fget o (nat_lit 2) (nat_lit 32)) c)))
    fun x2 =>
  sumN (nat_lit 16) fun d => strictN (TR (Nat.add (fget o (nat_lit 3) (nat_lit 32)) d)) fun td =>
  sumN (nat_lit 3) fun e => strictN (TR (Nat.add (fget o (nat_lit 4) (nat_lit 32)) e)) fun t =>
    cntVecA R8 R0 RY L8 L0 LY (ap3 x2 td t) (pc22 (pc22 x2 td) t)

end CFSG.KC.U6

end
