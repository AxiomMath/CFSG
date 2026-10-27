module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Main

public section

universe u v w

namespace CFSG.Open

open Matrix in
theorem _root_.CFSG.Milestones.cl_lit_aschbacher_proper_two_generated_core
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) (hrank : 3 ≤ pRank 2 (S : Subgroup G))
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≠ ⊤) :
    properTwoGenCoreGamma (S : Subgroup G) 1 ≠ ⊤ ∨ Nonempty (G ≃* properTwoGenCoreJ1) :=
  CFSG.ProperTwoGeneratedCore.Lemma37.aschbacher_proper_two_generated_core G hnonab S hrank hcore

end CFSG.Open
