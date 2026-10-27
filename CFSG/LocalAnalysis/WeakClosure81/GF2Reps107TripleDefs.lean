module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)

@[expose] def U43TripleGen : Prop :=
  ∀ (S : Type) [Group S] [Finite S], LieModel S .PSU 4 3 1 → ∀ d : S, d ^ 2 = 1 → d ≠ 1 →
    ∃ a b c : S, Subgroup.closure ({a * d * a⁻¹, b * d * b⁻¹, c * d * c⁻¹} : Set S) = ⊤

end CFSG.LocalAnalysis.WeakClosure81
