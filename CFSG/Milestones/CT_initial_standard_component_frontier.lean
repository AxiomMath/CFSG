module

public import CFSG.LocalAnalysis.ComponentInitial.FrontierFiveSporadic
public import CFSG.Sporadic.HNSchreier.SchreierCase
public import CFSG.Sporadic.Schreier.LySchreierCase
public import CFSG.Sporadic.ThSchreier.ThSchreierCase
public import CFSG.Sporadic.Schreier.BSchreierCase
public import CFSG.RankThree.PartOne.SPOR.Final

public section

universe u v w

namespace CFSG.Assembly.ComponentType

theorem _root_.CFSG.Milestones.ct_initial_standard_component_frontier
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper CFSG.Blueprint.Catalog G)
    (hrank : 3 ≤ twoRank G)
    (hcomp : IsComponentType G) (hB : LocalBProperty G) :
    (∃ t : G, orderOf t = 2 ∧ ∃ L : Subgroup G,
        IsComponentOf L (Subgroup.centralizer ({t} : Set G)) ∧ IsStandardSubgroup L) ∨
      (∃ z : G, orderOf z = 2 ∧ ∃ J : Subgroup G,
        IsComponentOf J (Subgroup.centralizer ({z} : Set G)) ∧ z ∈ J ∧
          ∃ r : ℕ, 3 ≤ r ∧ ∃ S : Sylow 2 J,
            Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :=
  CFSG.LocalAnalysis.ComponentInitial.initial_standard_component_frontier_of_five_sporadic
    CFSG.Sporadic.HNSchreier.sporadicSchreierCase_HN
    CFSG.Sporadic.LySchreier.sporadicSchreierCase_Ly
    CFSG.Sporadic.ThSchreier.sporadicSchreierCase_Th
    CFSG.Sporadic.BSchreier.sporadicSchreierCase_B
    CFSG.RankThree.PartOne.SPOR.sporadicSchreierCase_M
    G hnonab hK hrank hcomp hB

end CFSG.Assembly.ComponentType
