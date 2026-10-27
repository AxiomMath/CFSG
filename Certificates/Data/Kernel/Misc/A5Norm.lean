module

public import Certificates.Data.Kernel.Misc.Sp4Cen

public section

namespace CFSG.KD.A5Norm

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GL4

@[expose] noncomputable def bitB (x q : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight x q) 1) 1

@[expose] noncomputable def selP (b : Bool) (p : Nat) : Nat := Bool.rec (motive := fun _ => Nat) 0 p b

@[expose] noncomputable def dP (P : Nat → Nat) (x y i j : Nat) : Nat :=
  CFSG.KC.Misc.letN (Nat.mul 4 i) fun r =>
    Nat.xor
      (Nat.xor
        (Nat.xor (selP (bitB x j) (P r)) (selP (bitB x (Nat.add 4 j)) (P (Nat.add r 1))))
        (Nat.xor (selP (bitB x (Nat.add 8 j)) (P (Nat.add r 2)))
          (selP (bitB x (Nat.add 12 j)) (P (Nat.add r 3)))))
      (Nat.xor
        (Nat.xor (selP (bitB y r) (P j)) (selP (bitB y (Nat.add r 1)) (P (Nat.add 4 j))))
        (Nat.xor (selP (bitB y (Nat.add r 2)) (P (Nat.add 8 j)))
          (selP (bitB y (Nat.add r 3)) (P (Nat.add 12 j)))))

@[expose] noncomputable def dAcc (P : Nat → Nat) (x y : Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun q acc => Nat.lor acc (dP P x y (Nat.div q 4) (Nat.mod q 4))) n

@[expose] noncomputable def eqP (P : Nat → Nat) (t x y : Nat) : Nat := Nat.xor t (dAcc P x y 16)

@[expose] noncomputable def orL (l : List Nat) (f : Nat → Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun a _ acc => Nat.lor (f a) acc) l

@[expose] noncomputable def orN (m : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun u acc => Nat.lor acc (f u)) m

@[expose] noncomputable def injP (P : Nat → Nat) (t : Nat) : Nat :=
  Nat.xor t (orN 15 fun u => eqP P t (colC (Nat.succ u)) 0)

@[expose] noncomputable def bitsL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun a _ acc => Nat.lor (Nat.shiftLeft 1 a) acc) l

@[expose] noncomputable def memB (S c : Nat) : Bool := Nat.blt 0 (Nat.land S (Nat.shiftLeft 1 c))

@[expose] noncomputable def withP (k : (Nat → Nat) → Nat → Bool) : Bool :=
  CFSG.KC.F4M3B.frc (Nat.sub (Nat.pow 2 (Nat.pow 2 16)) 1) fun t =>
  CFSG.KC.F4M3B.frc (CFSG.KC.F4M3B.pln 0 16) fun p0 =>
  CFSG.KC.F4M3B.frc (CFSG.KC.F4M3B.pln 1 16) fun p1 =>
  CFSG.KC.F4M3B.frc (CFSG.KC.F4M3B.pln 2 16) fun p2 =>
  CFSG.KC.F4M3B.frc (CFSG.KC.F4M3B.pln 3 16) fun p3 =>
  CFSG.KC.F4M3B.frc (CFSG.KC.F4M3B.pln 4 16) fun p4 =>
  CFSG.KC.F4M3B.frc (CFSG.KC.F4M3B.pln 5 16) fun p5 =>
  CFSG.KC.F4M3B.frc (CFSG.KC.F4M3B.pln 6 16) fun p6 =>
  CFSG.KC.F4M3B.frc (CFSG.KC.F4M3B.pln 7 16) fun p7 =>
  CFSG.KC.F4M3B.frc (CFSG.KC.F4M3B.pln 8 16) fun p8 =>
  CFSG.KC.F4M3B.frc (CFSG.KC.F4M3B.pln 9 16) fun p9 =>
  CFSG.KC.F4M3B.frc (CFSG.KC.F4M3B.pln 10 16) fun p10 =>
  CFSG.KC.F4M3B.frc (CFSG.KC.F4M3B.pln 11 16) fun p11 =>
  CFSG.KC.F4M3B.frc (CFSG.KC.F4M3B.pln 12 16) fun p12 =>
  CFSG.KC.F4M3B.frc (CFSG.KC.F4M3B.pln 13 16) fun p13 =>
  CFSG.KC.F4M3B.frc (CFSG.KC.F4M3B.pln 14 16) fun p14 =>
  CFSG.KC.F4M3B.frc (CFSG.KC.F4M3B.pln 15 16) fun p15 =>
    k (fun q => lAt [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] q) t

@[expose] noncomputable def subP (t X S : Nat) : Bool := Nat.beq (Nat.land X (Nat.xor t S)) 0

@[expose] noncomputable def compC (hs cs : List Nat) (a b : Nat) (P : Nat → Nat) (t : Nat) : Bool :=
  subP t (Nat.land (Nat.land (injP P t) (orL hs fun y => eqP P t a y)) (orL hs fun y => eqP P t b y))
    (bitsL cs)

@[expose] noncomputable def centC (a b : Nat) (P : Nat → Nat) (t : Nat) : Bool :=
  subP t (Nat.land (Nat.land CFSG.KD.Sp4Cen.sqPlane (eqP P t a a)) (eqP P t b b))
    (Nat.shiftLeft 1 id4)

@[expose] noncomputable def fixC (a b : Nat) : Bool :=
  allN 16 fun u => impB (andB (Nat.beq (mul4F a (colC u)) (colC u))
    (Nat.beq (mul4F b (colC u)) (colC u))) (Nat.beq u 0)

@[expose] noncomputable def incF (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun a _ ih p => andB (Nat.blt p a) (ih a)) l

@[expose] noncomputable def incL (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a l _ => incF l a) l

@[expose] noncomputable def grpC (cs : List Nat) : Bool :=
  CFSG.KC.LQT.P.letB (bitsL cs) fun S =>
    andB (allL cs fun c => Nat.blt c 65536) (andB (incL cs) (andB (CFSG.KC.Misc.memN id4 cs)
      (andB (allL cs fun x => allL cs fun y => memB S (mul4F x y))
        (allL cs fun x => anyL cs fun y => Nat.beq (mul4F x y) id4))))

@[expose] noncomputable def subC (ts cs : List Nat) : Bool :=
  allL ts fun c => CFSG.KC.Misc.memN c cs

@[expose] noncomputable def freeC (cs ts : List Nat) : Bool :=
  allL cs fun d => orB (Nat.beq d id4) (orB (notB (Nat.beq (mul4F (mul4F d d) d) id4))
    (anyL ts fun t => allL ts fun t' => notB (Nat.beq (mul4F d t) (mul4F t' d))))

@[expose] noncomputable def transC (hs us : List Nat) (v0 : Nat) : Bool :=
  allL us fun u => anyL hs fun c => Nat.beq (mul4F c (colC v0)) (colC u)

end CFSG.KD.A5Norm

end
