module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def s16h_H5ZCond {W : Type} [CommGroup W] (A L : Subgroup (MulAut W)) : Prop :=
  commSub ⊤ L ⊓ fixV L = ⊥ ∨
    ∀ T : Subgroup (MulAut W), T ≤ A ⊓ normalizer (L : Set (MulAut W)) →
      (∀ g ∈ A ⊓ normalizer (L : Set (MulAut W)), ∀ x ∈ T, g * x * g⁻¹ ∈ T) →
      (∀ x ∈ T, ∃ n : ℕ, x ^ 2 ^ n ∈ centSub (commSub ⊤ L ⊓ fixV L)) →
      (∃ f ∈ A ⊓ normalizer (L : Set (MulAut W)), ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
        f ∉ centSub (commSub ⊤ L ⊓ fixV L) ∧ f ^ q ∈ centSub (commSub ⊤ L ⊓ fixV L)) →
      T ≤ centSub (commSub ⊤ L ⊓ fixV L)

@[expose] def K_JonesParshallH1 : Prop :=
  ∀ (X : Type) [CommGroup X] [Finite X], (∀ x : X, x ^ 2 = 1) →
    ∀ L : Subgroup (MulAut X),
      ((s16h_H5RowA5 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ∨
        s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2 ∨
        s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3 ∨
        (s16h_H5RowSt8 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ∧ commSub ⊤ L ∈ irrSet L)) →
        commSub ⊤ L ⊓ fixV L = ⊥) ∧
      (s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2 →
        rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
