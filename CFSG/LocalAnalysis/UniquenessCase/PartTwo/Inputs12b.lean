module

public import CFSG.LocalAnalysis.WeakClosure81.EightDefs
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.WeakClosure81

@[expose] def W3Lem86_1 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V H T : Subgroup G, Hyp7 V → IsCalH V H → ¬ IsCalH0 V H →
    IsSylowIn 2 T (H ⊓ normalizer (V : Set G)) → E3.wClos V 0 T ≠ V →
    (CentralizersInM V H T ∨ NormalizersInM V H (E3.wClos V 0 T)) →
    H = (H ⊓ normalizer (V : Set G)) ⊔ (H ⊓ normalizer (E3.wClos V 0 T : Set G)) ∧
      ¬ H ≤ normalizer (V : Set G)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
