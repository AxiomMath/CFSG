module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowO4aTA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H

theorem s16h_H5O4a_torus {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ 2)
    {b c : K} :
    ∃ z ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)), z ≠ 1 ∧ z ^ 3 = 1 ∧
      (∃ e : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K, e ≠ 0 ∧ StatedQuadMinus 2 K b c e = 0 ∧
        ∃ ω : K, ω ≠ 0 ∧ toAddMap z e = ω • e) ∧
      ∀ t : K, t ≠ 0 → ∃ x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K,
        StatedQuadMinus 2 K b c x = t ∧ toAddMap z x = x :=
  s16h_H5O4a_torus_proof hK

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
