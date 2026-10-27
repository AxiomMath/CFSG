module

public import CFSG.CGT.M24R.N8Inputs
public import Certificates.Data.Kernel.F4M3B
public import Mathlib

public section

namespace CFSG.KC.N8K

open CFSG.CosetTable CFSG.CGT.T75JM CFSG.CGT.M24R CFSG.KC.F4M3B

abbrev carmR6 := carmRels8

abbrev carmR5 := restrictWords (subsetOf _ [0, 1, 2, 3, 4]) carmR6

abbrev carmR4 := restrictWords (subsetOf _ [0, 1, 2, 3]) carmR5

abbrev carmR3 := restrictWords (subsetOf _ [0, 1, 2]) carmR4

abbrev carmR2 := restrictWords (subsetOf _ [0, 1]) carmR3

abbrev carmR1 := restrictWords (subsetOf _ [0]) carmR2

@[expose] def glV (A B C D : Cols) (v : Nat) : Nat :=
  Nat.lor (Nat.lor (applyC A v) (applyC B v)) (Nat.lor (applyC C v) (applyC D v))

@[expose] def glAnd (A B C D : Cols) (t : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) t fun n acc => frcN acc fun a => Nat.land a (glV A B C D (n + 1))

@[expose] noncomputable def glPlaneN (n : Nat) : Nat :=
  frcN (pln 0 16) fun p0 => frcN (pln 1 16) fun p1 => frcN (pln 2 16) fun p2 =>
  frcN (pln 3 16) fun p3 => frcN (pln 4 16) fun p4 => frcN (pln 5 16) fun p5 =>
  frcN (pln 6 16) fun p6 => frcN (pln 7 16) fun p7 => frcN (pln 8 16) fun p8 =>
  frcN (pln 9 16) fun p9 => frcN (pln 10 16) fun p10 => frcN (pln 11 16) fun p11 =>
  frcN (pln 12 16) fun p12 => frcN (pln 13 16) fun p13 => frcN (pln 14 16) fun p14 =>
  frcN (pln 15 16) fun p15 =>
    glAnd ⟨p0, p4, p8, p12⟩ ⟨p1, p5, p9, p13⟩ ⟨p2, p6, p10, p14⟩ ⟨p3, p7, p11, p15⟩
      (Nat.sub (Nat.pow 2 (Nat.pow 2 16)) 1) n

@[expose] noncomputable def glPlane : Nat := glPlaneN 15

@[expose] def popc : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => Nat.land x 1) fun k ih x =>
    Nat.add (ih (Nat.land x (Nat.sub (Nat.pow 2 (Nat.pow 2 k)) 1)))
      (ih (Nat.shiftRight x (Nat.pow 2 k)))

@[expose] noncomputable def glCountK : Bool := Nat.beq (popc 16 glPlane) 20160

@[expose] def letter8 (n : Nat) : Fin 6 :=
  ⟨Nat.mod (Nat.add (Nat.land n 7) 5) 6, Nat.mod_lt _ (by decide)⟩

@[expose] def decW : Nat → Nat → List (Fin 6) :=
  Nat.rec (motive := fun _ => Nat → List (Fin 6)) (fun _ => []) fun _ ih n =>
    Bool.rec (letter8 n :: ih (Nat.shiftRight n 3)) [] (Nat.beq n 0)

@[expose] def stepC (i : Fin 6) (x : Nat) : Nat := colsCode8 (compC (modelCols8 i) (colsOfCode8 x))

@[expose] def glTab : Nat :=
  6153085089567244699372504859236204124035100518475482834412386122397017209080142328746755592227471707574273289930400

@[expose] def lk (i v : Nat) : Nat :=
  Nat.land (Nat.shiftRight glTab (Nat.mul 4 (Nat.add (Nat.mul 16 i) v))) 15

@[expose] def stepT (i x : Nat) : Nat :=
  Nat.add (Nat.add (Nat.add (lk i (Nat.mod x 16)) (Nat.mul 16 (lk i (Nat.mod (Nat.div x 16) 16))))
    (Nat.mul 256 (lk i (Nat.mod (Nat.div x 256) 16)))) (Nat.mul 4096 (lk i (Nat.mod (Nat.div x 4096) 16)))

@[expose] def evalC : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => colsCode8 idC) fun _ ih n =>
    Bool.rec (frcN (ih (Nat.shiftRight n 3)) (stepT (letter8 n).val)) (colsCode8 idC)
      (Nat.beq n 0)

@[expose] def glFreshK (k : Nat → Nat → Bool) : List Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) k
    fun n _ ih lo cnt => frc (evalC 12 n) fun c =>
      Bool.and (Nat.ble lo c) (frc (Nat.succ c) fun lo' => frc (Nat.succ cnt) fun cnt' => ih lo' cnt')

@[expose] def glEnd (_ cnt : Nat) : Bool := Nat.beq cnt 20160

@[expose] def glFresh (Ls : List (List Nat)) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) glEnd (fun L _ ih => glFreshK ih L) Ls

end CFSG.KC.N8K

end
