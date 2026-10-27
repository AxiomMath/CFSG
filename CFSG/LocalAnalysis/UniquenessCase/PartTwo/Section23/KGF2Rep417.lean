module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Lie

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin Subgroup

@[expose] def K_GF2Rep417 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (X T L : Subgroup (MulAut W)) (n : ℕ),
      IsSylowIn 2 T X → IsComponentOf L X → CFSG.pCore 2 ↥L = ⊥ → CFSG.pCore 2 ↥X = ⊥ →
      L ⊔ T = X →
      (IsL2 ↥L n ∨ IsSz ↥L n ∨ IsSU3 ↥L n ∨
        ((IsSL3 ↥L n ∨ IsSp4 ↥L n) ∧ ∃ t ∈ T, ActsNontrivOnDiagramIn L t)) →
      fixV T ≠ fixV X →
      ∀ A ∈ E3.aSet (n + 1) X, A ≤ Subgroup.centralizer (L : Set (MulAut W))

end CFSG.LocalAnalysis.UniquenessCase.UC22
