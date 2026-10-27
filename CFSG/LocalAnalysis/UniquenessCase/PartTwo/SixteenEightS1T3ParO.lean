module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def s16t3Flag {k : ℕ} {R K : Type} [Zero K] (i : ℕ) : Set (Fin k ⊕ R → K) :=
  {v | ∀ c, v c ≠ 0 → ∃ j : Fin k, c = Sum.inl j ∧ (j : ℕ) < i}

@[expose] def s16t3Borel {k : ℕ} {R K : Type} [Fintype R] [DecidableEq R] [Field K]
    (Q : (Fin k ⊕ R → K) → K) (d : ℕ) : Set (Matrix.GeneralLinearGroup (Fin k ⊕ R) K) :=
  {y | (∀ v, Q (Matrix.mulVec (y : Matrix (Fin k ⊕ R) (Fin k ⊕ R) K) v) = Q v) ∧
    ∀ i, 1 ≤ i → i ≤ d → ∀ v ∈ s16t3Flag (k := k) (R := R) (K := K) i,
      Matrix.mulVec (y : Matrix (Fin k ⊕ R) (Fin k ⊕ R) K) v ∈
        s16t3Flag (k := k) (R := R) (K := K) i}

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
