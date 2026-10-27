module

public import CFSG.ClassicalGroups.Orthogonal.SumSquaresDefs
public import CFSG.Open.PGLModelDefs
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Orth6Minus

open CFSG.ClassicalGroups.Orthogonal

abbrev Six : Type := Fin 2 ⊕ Fin 2 ⊕ Fin 2

@[expose] def coord : Fin 6 → Six :=
  ![Sum.inl 0, Sum.inl 1, Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1), Sum.inr (Sum.inr 0),
    Sum.inr (Sum.inr 1)]

@[expose] def permA : Equiv.Perm Six :=
  Equiv.swap (coord 0) (coord 1) * Equiv.swap (coord 2) (coord 3)

@[expose] def permC : Equiv.Perm Six :=
  Equiv.swap (coord 2) (coord 4) * Equiv.swap (coord 3) (coord 5)

abbrev orthSix (K : Type*) [Field K] : Subgroup (GL Six K) :=
  CFSG.PGLModel.orthogonalGroup (sumSqForm (ι := Six) (K := K))

@[expose] def tGL (K : Type*) [Field K] : GL Six K := negCoordGL {coord 0, coord 1}

@[expose] def gens (K : Type*) [Field K] : Set (GL Six K) :=
  {g | ∃ r s : Six, r ≠ s ∧ g = negCoordGL {r, s}} ∪
    {TauCeti.permutationGL permA, TauCeti.permutationGL permC}

end CFSG.LocalAnalysis.WeakClosure81.Orth6Minus
