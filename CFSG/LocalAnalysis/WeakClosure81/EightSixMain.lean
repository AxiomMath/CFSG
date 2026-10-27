module

public import CFSG.LocalAnalysis.WeakClosure81.EightSixDefs
public import CFSG.LocalAnalysis.WeakClosure81.W15Seven

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def W3Borel86 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V H T : Subgroup G, Hyp7 V → IsCalH V H → ¬ IsCalH0 V H →
    IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)) → H = kGenIn V H ⊔ T →
    E3.wClos V 0 T ≠ V →
    (CentralizersInM V H T ∨ NormalizersInMTwo V H (E3.wClos V 0 T)) →
      ¬ Shape86Delta V H T

end CFSG.LocalAnalysis.WeakClosure81

end
