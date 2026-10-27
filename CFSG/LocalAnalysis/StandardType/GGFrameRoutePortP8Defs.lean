module

public import CFSG.Assembly.LargeEvenDefs

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly

@[expose] def GGFrameJTag (lab : LargeEvenLabel) : Prop :=
  lab = ⟨.twA, 4, 1⟩ ∨ lab = ⟨.twA, 5, 1⟩ ∨ lab = ⟨.twA, 6, 1⟩ ∨ lab = ⟨.twD, 5, 1⟩

@[expose] def GGFrameInd {K R : Type} [Group K] [Group R] (I : Set (MulAut R))
    (θ : K ⧸ Subgroup.center K ≃* R) (α : MulAut K) : Prop :=
  ∃ φ ∈ I, ∀ k : K, φ (θ (QuotientGroup.mk k)) = θ (QuotientGroup.mk (α k))

end CFSG.StandardType.FrameRoute
