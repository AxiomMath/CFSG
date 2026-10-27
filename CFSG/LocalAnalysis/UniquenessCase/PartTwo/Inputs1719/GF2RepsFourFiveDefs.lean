module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup

@[expose] def W4Lem4_5K : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y H T A K : Subgroup (MulAut W)) (Ω : Set (Subgroup (MulAut W))) (j : ℕ),
      H ≤ Y → IsSylowIn 2 T H →
      (∀ B ∈ Ω, ∀ g ∈ Y, B.map (MulAut.conj g).toMonoidHom ∈ Ω) →
      (∀ B ∈ Ω, B ∈ E3.aSet (j + 1) Y) →
      A ∈ Ω → A ≤ T → E1.IsE j H T A K →
      commSub (fixV (Wk j T Ω)) (twoResidual K) = ⊥

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
