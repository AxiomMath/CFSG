module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155L143

@[expose] def L143EigProp : Prop :=
  ∀ (K : Type) [Field K] (ω : K), ω ^ 3 = 1 → ω ≠ 1 → ∀ a : Matrix (Fin 3) (Fin 3) K,
    a ^ 3 = 1 → a.det = 1 → (∀ c : K, a ≠ Matrix.scalar (Fin 3) c) →
      ∃ P : Matrix (Fin 3) (Fin 3) K, IsUnit P.det ∧ a * P = P * Matrix.diagonal ![1, ω, ω ^ 2]

end CFSG.RankThree.PartTwo.Sec15.Sylow155L143
