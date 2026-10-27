module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.RealizeCheck
public import Certificates.Data.Kernel.MinusSecondKind

public section

namespace CFSG.KD.MinusRealize

open CFSG.OddTranspositions.PartThree.MinusRealize CFSG.KD.MinusQuandle CFSG.KD.MinusSecondKind

@[expose] def anyF (n : ℕ) (g : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun k acc => Bool.rec (motive := fun _ => Bool) acc true (g k)) n

@[expose] def dg (c k : ℕ) : ℕ := Nat.mod (Nat.div c (Nat.pow 5 k)) 5

@[expose] def mk4 (a b c d : ℕ) : ℕ :=
  Nat.add a (Nat.add (Nat.mul 5 b) (Nat.add (Nat.mul 25 c) (Nat.mul 125 d)))

@[expose] def qf (c d : ℕ) : ℕ :=
  Nat.mod (Nat.add (Nat.mul (dg c 0) (dg d 0)) (Nat.add (Nat.mul (dg c 1) (dg d 1))
    (Nat.add (Nat.mul (dg c 2) (dg d 2)) (Nat.mul 3 (Nat.mul (dg c 3) (dg d 3)))))) 5

@[expose] def sm (s c : ℕ) : ℕ :=
  mk4 (Nat.mod (Nat.mul s (dg c 0)) 5) (Nat.mod (Nat.mul s (dg c 1)) 5)
    (Nat.mod (Nat.mul s (dg c 2)) 5) (Nat.mod (Nat.mul s (dg c 3)) 5)

@[expose] def subK (k c d : ℕ) : ℕ :=
  mk4 (Nat.mod (Nat.add (dg d 0) (Nat.mul 4 (Nat.mul k (dg c 0)))) 5)
    (Nat.mod (Nat.add (dg d 1) (Nat.mul 4 (Nat.mul k (dg c 1)))) 5)
    (Nat.mod (Nat.add (dg d 2) (Nat.mul 4 (Nat.mul k (dg c 2)))) 5)
    (Nat.mod (Nat.add (dg d 3) (Nat.mul 4 (Nat.mul k (dg c 3)))) 5)

@[expose] def rf (c d : ℕ) : ℕ :=
  force (Nat.mod (Nat.mul 2 (Nat.mul (qf c d) (Nat.pow (qf c c) 3))) 5) fun k => subK k c d

@[expose] def codeA (v : Array ℕ) : ℕ := mk4 v[0]! v[1]! v[2]! v[3]!

@[expose] def vA (π : Bool) (i : ℕ) : Array ℕ :=
  (if π then minusSquareVecs else minusNonsquareVecs)[i]!

@[expose] def pk (π : Bool) : ℕ := orF 65 fun i => Nat.shiftLeft (codeA (vA π i)) (Nat.mul 10 i)

@[expose] def cd (P i : ℕ) : ℕ := Nat.land (Nat.shiftRight P (Nat.mul 10 i)) 1023

@[expose] def pinRow (P i : ℕ) (v : Array ℕ) : Bool :=
  bAnd (Nat.beq (cd P i) (codeA v)) (allF 4 fun k => Nat.blt v[k]! 5)

@[expose] def pinOK (π : Bool) (P : ℕ) : Bool :=
  allF 65 fun i => pinRow P i (vA π i)

@[expose] def sgn (π : Bool) (q : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) (bOr (Nat.beq q 2) (Nat.beq q 3))
    (bOr (Nat.beq q 1) (Nat.beq q 4)) π

@[expose] def signOK (π : Bool) (P : ℕ) : Bool :=
  allF 65 fun i => force (cd P i) fun c => sgn π (qf c c)

@[expose] def tableOK (R : ℕ → ℕ) (P : ℕ) : Bool :=
  allF 65 fun i => force (cd P i) fun ci => force (R i) fun ri => allF 65 fun j =>
    force (cd P j) fun cj =>
      bAnd (force (rf ci cj) fun w => force (cd P (ln ri j)) fun ct =>
          anyF 4 fun s => Nat.beq (sm (Nat.succ s) w) ct)
        (bOr (Nat.beq i j) (allF 4 fun s => bNot (Nat.beq (sm (Nat.succ s) cj) ci)))

@[expose] def coverOK (π : Bool) (P : ℕ) : Bool :=
  allF 625 fun x => force (qf x x) fun q => bOr (bNot (sgn π q))
    (anyF 65 fun i => force (cd P i) fun c => anyF 4 fun s => Nat.beq (sm (Nat.succ s) c) x)

end CFSG.KD.MinusRealize
