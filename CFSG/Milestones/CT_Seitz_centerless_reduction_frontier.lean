module

public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.Blueprint.EvenStandardExact
public import CFSG.Blueprint.EvenBNRankTwoExact
import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesFinalHolds
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

universe u v w

namespace CFSG.Open

theorem _root_.CFSG.Milestones.ct_seitz_centerless_reduction_frontier
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (L : Subgroup G) (hL : standardComponentIsStandard L)
    (hcore : ∀ t : G, orderOf t = 2 →
      standardComponentOddCore (Subgroup.centralizer ({t} : Set G)) = ⊥)
    (S : Sylow 2 (Subgroup.centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))))
    (htype : Blueprint.Recognition.Exact.EvenStandardType (L ⧸ Subgroup.center L))
    (hexc : ¬ Blueprint.Recognition.Exact.EvenStandardException (L ⧸ Subgroup.center L))
    (hZ : Subgroup.center L = ⊥) :
    Blueprint.NativeSporadic.SporadicRep L ∨ Blueprint.Recognition.Exact.EvenBNRankTwoType L ∨
      (Blueprint.LieModel L .PSp 3 2 1 ∨ Blueprint.LieModel L .PSU 6 2 1 ∨
        Blueprint.LieModel L .POmegaMinus 4 2 1 ∨ Blueprint.LieModel L .POmegaPlus 4 2 1) :=
  CFSG.SeitzReduction.seitz_reduction_holds G hnonab hK L hL hcore S hS htype hexc hZ

end CFSG.Open
