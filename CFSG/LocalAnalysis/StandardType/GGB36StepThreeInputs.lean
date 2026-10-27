module

public import CFSG.LocalAnalysis.StandardType.GGB36Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGInnerOnD4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (A : Subgroup (MulAut X)) (σ : MulAut X) (J : Subgroup X),
    IsElemAbelian 3 A → σ ∈ A → IsComponentOf J (ggAutFixedSubgroup σ) → (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) →
    LargeEvenMarking X (fun lab _ _ I _ θ => ¬ (lab.tag = .E6 ∨ lab.tag = .twE6) ∧ GGInducedInn A θ I) →
    ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ → labJ.tag = .D → labJ.rank = 4 →
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → ∀ a ∈ A, ∃ u ∈ J, ∀ v ∈ J, a v = u * v * u⁻¹

end CFSG.StandardType

end
