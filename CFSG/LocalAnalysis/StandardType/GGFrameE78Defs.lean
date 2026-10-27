module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

public section

namespace CFSG.StandardType.FrameRoute

abbrev FEMat (n : ℕ) : Type := Matrix (Fin n) (Fin n) (ZMod 3)

abbrev FEVec (n : ℕ) : Type := Fin n → ZMod 3

@[expose] def feS (n : ℕ) (i : Fin n) : FEMat n :=
  fun p q => (if p = q then 1 else 0) - (if q = i then ((CartanMatrix.E n p i : ℤ) : ZMod 3) else 0)

inductive FEConjDer (n : ℕ) : FEMat n → Prop
  | base (i : Fin n) : FEConjDer n (feS n i)
  | conj (i : Fin n) {r : FEMat n} (h : FEConjDer n r) : FEConjDer n (feS n i * r * feS n i)

@[expose] def feT (n : ℕ) : Set (FEMat n) := {r | FEConjDer n r}

@[expose] def feTx (n : ℕ) (x : FEVec n) : Set (FEMat n) := {r | r ∈ feT n ∧ r.mulVec x = x}

end CFSG.StandardType.FrameRoute

end
