module

public import Certificates.Data.YamakiEnum
public import Certificates.Data.FoxCodes
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

namespace CFSG.CGT.Foote82.OmegaSix

open Matrix CFSG.ClassicalInvolution.Solomon73.Yamaki

@[expose] def bit6 : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → Fin 6
  | .inl i => ⟨i.val, by omega⟩
  | .inr (.inl i) => ⟨2 + i.val, by omega⟩
  | .inr (.inr i) => ⟨4 + i.val, by omega⟩

@[expose] def cvec (n : ℕ) : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2 :=
  fun a => if n.testBit (bit6 a).val then 1 else 0

@[expose] def vcode (v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) : ℕ :=
  (v (.inl 0)).val + 2 * (v (.inl 1)).val + 4 * (v (.inr (.inl 0))).val +
    8 * (v (.inr (.inl 1))).val + 16 * (v (.inr (.inr 0))).val + 32 * (v (.inr (.inr 1))).val

@[expose] def marr (A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
    Array ℕ :=
  Array.ofFn (n := 64) fun n => vcode (A *ᵥ cvec n.val)

@[expose] def ofBits (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  M.submatrix bit6 bit6

@[expose] def aMat : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![1, 0, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0; 1, 0, 1, 1, 0, 1;
    0, 0, 0, 1, 0, 0; 1, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]

@[expose] def bMat : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 1, 1, 1, 1, 1;
    1, 1, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1; 0, 1, 1, 0, 0, 1]

@[expose] def c1Mat : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 0, 0;
    1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]

@[expose] def c2Mat : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1]

@[expose] def d1Mat : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1]

@[expose] def d2Mat : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 1, 0; 0, 1, 1, 1, 1, 1;
    1, 1, 0, 1, 0, 1; 1, 1, 0, 0, 1, 1; 1, 0, 0, 1, 1, 1]

@[expose] def involCheck (_ : Unit := ()) : Bool :=
  decide (aMat * aMat = 1) && decide (bMat * (bMat * (bMat * (bMat * bMat))) = 1) &&
    decide (c1Mat * c1Mat = 1) && decide (c2Mat * c2Mat = 1) && decide (d1Mat * d1Mat = 1) &&
    decide (d2Mat * d2Mat = 1)

@[expose] def q6 (v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) : ZMod 2 :=
  v (.inl 0) * v (.inr (.inl 0)) + v (.inl 1) * v (.inr (.inl 1)) + v (.inr (.inr 0)) ^ 2 +
    v (.inr (.inr 0)) * v (.inr (.inr 1)) + v (.inr (.inr 1)) ^ 2

@[expose] def isomB (A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) : Bool :=
  decide (∀ v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2, q6 (A *ᵥ v) = q6 v)

@[expose] def isomCheck (_ : Unit := ()) : Bool :=
  isomB c1Mat && isomB c2Mat && isomB d1Mat && isomB d2Mat

@[expose] def commCheck (_ : Unit := ()) : Bool :=
  decide (c1Mat * c2Mat * c1Mat * c2Mat = aMat) && decide (d1Mat * d2Mat * d1Mat * d2Mat = bMat)

@[expose] def genA6 (_ : Unit := ()) : Array (Array ℕ) := #[marr aMat, marr bMat]

@[expose] def omegaEnum (_ : Unit := ()) : Enum := bfsEnum (genA6 ()) 25920

@[expose] def enumCheck (_ : Unit := ()) : Bool :=
  let gs := genA6 ()
  let E := omegaEnum ()
  enumOK E gs && E.elems.size == 25920

@[expose] def relators : List (List ℕ) :=
  [[0, 0], [1, 1, 1, 1, 1],
    [0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1]]

@[expose] def relCheck (_ : Unit := ()) : Bool :=
  let gs := genA6 ()
  relators.all fun w => wordA gs w == idA ()

@[expose] def foxCheck (_ : Unit := ()) : Bool :=
  CFSG.CGT.Foote82.FoxH1.foxCheck2 64 (genA6 ()) relators

end CFSG.CGT.Foote82.OmegaSix
