module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def S1614OmFrame {ι K : Type} [Field K] (Q : QuadraticForm K (ι → K))
    (a a' x x' : ι → K) : Prop :=
  Q a = 1 ∧ Q a' = 1 ∧ Q x = 1 ∧ Q x' = 1 ∧
    QuadraticMap.polar Q a a' = 1 ∧ QuadraticMap.polar Q x x' = 1 ∧
    QuadraticMap.polar Q a x = 0 ∧ QuadraticMap.polar Q a x' = 0 ∧
    QuadraticMap.polar Q a' x = 0 ∧ QuadraticMap.polar Q a' x' = 0

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
