module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

@[expose] def GGReflConjSimple {G : Type} [Group G] [Finite G] {Bs : Subgroup G} (p : ℕ)
    {Λ : Type} (A : Subgroup (MulAut ↥Bs)) (φ : Λ → MulAut ↥Bs) : Prop :=
  ∀ t ∈ A, GGIsReflection p t → ∃ w ∈ A, ∃ i, t = w * φ i * w⁻¹

end CFSG.StandardType
