module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_FixHalfRows : Prop :=
  (∀ (X : Type) [CommGroup X] [Finite X], (∀ x : X, x ^ 2 = 1) →
    ∀ L : Subgroup (MulAut X),
      (s16h_H5RowL3 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ∨
        s16h_H5RowA5 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ∨
        s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2 ∨
        s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3 ∨
        s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2 ∨
        s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3 ∨
        (s16h_H5RowSt8 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ∧ commSub ⊤ L ∈ irrSet L)) →
      3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L)) ∧
  (∀ (X : Type) [CommGroup X] [Finite X], (∀ x : X, x ^ 2 = 1) →
    ∀ (L : Subgroup (MulAut X)) (U Z : Subgroup X) (n : ℕ), 6 ≤ n → n ≤ 8 →
      IsAlt ↥L n → (∀ l ∈ L, ∀ u ∈ U, l u ∈ U) → commSub U L = U → Z ≤ fixV L →
      SumOfNat (fun H U Z => AlternatingNatural H U Z n) L U Z 2 → rk ↥Z ≤ 2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
