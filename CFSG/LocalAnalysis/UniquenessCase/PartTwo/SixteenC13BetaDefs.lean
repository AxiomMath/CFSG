module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBTrans

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

@[expose] def s16c13betaGood {W : Type*} [CommGroup W] (X : Subgroup (MulAut W)) (p n N : ℕ) :
    Prop :=
  ∀ φ ∈ X, (∃ a : ℕ, orderOf φ = 2 ^ a) → rkIdx (fixV (Subgroup.zpowers φ)) ≤ N →
    ∀ U : Subgroup W, rkIdx U ≤ n → ¬ U ≤ fixV (Subgroup.zpowers φ) →
      ∃ z ∈ s16n9bCommOn U φ, z ≠ 1 ∧
        ∃ E : Subgroup (MulAut W), E ≤ X ∧ IsPGroup p ↥E ∧ ¬ IsCyclic ↥E ∧ ∀ e ∈ E, e z = z

@[expose] def s16c13betaPts {W : Type*} [CommGroup W] (X : Subgroup (MulAut W)) (p n : ℕ) :
    Prop :=
  ∀ U : Subgroup W, rkIdx U ≤ n →
    ∃ z ∈ U, z ≠ 1 ∧ ∃ E : Subgroup (MulAut W), E ≤ X ∧ IsPGroup p ↥E ∧ ¬ IsCyclic ↥E ∧
      ∀ e ∈ E, e z = z

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
