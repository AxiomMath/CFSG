module

public import CFSG.RankThree.PartTwo.Notation
import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy
import CFSG.RankThree.PartOne.S9.Sylow.ResidualBridge

public section

namespace CFSG.RankThree.PartTwo

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

theorem dichotomy_of_mem_thetaComponentsIn {H Y K : Subgroup G}
    (hY : Y ∈ thetaComponentsIn H) (hK : K ∈ thetaComponentsIn H) :
    Y ≤ K ∨ (K ≤ Subgroup.normalizer (Y : Set G) ∧
      ⁅Y, K⁆ ≤ inSubgroup (aschbacherSolvableCore 3) Y) := by
  obtain ⟨hYH, hY'⟩ := mem_thetaComponentsIn_iff.mp hY
  obtain ⟨hKH, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  rcases GroupTheory.theta_component_subnormal_subgroup_dichotomy Nat.prime_three hY' hK'.2.1 with
    hle | ⟨hnorm, hcomm⟩
  · left
    have h1 := Subgroup.map_mono (f := H.subtype) hle
    rwa [Subgroup.map_subgroupOf_eq_of_le hYH,
      Subgroup.map_subgroupOf_eq_of_le hKH] at h1
  · right
    refine ⟨?_, ?_⟩
    · have h1 := (Subgroup.map_mono (f := H.subtype) hnorm).trans
          (Subgroup.le_normalizer_map H.subtype)
      rwa [Subgroup.map_subgroupOf_eq_of_le hYH,
        Subgroup.map_subgroupOf_eq_of_le hKH] at h1
    · have h1 := Subgroup.map_mono (f := H.subtype) hcomm
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hYH,
        Subgroup.map_subgroupOf_eq_of_le hKH,
        PartOne.Sec9A.map_inSubgroup_theta_of_injective Nat.prime_three H.subtype
          H.subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le hYH] at h1
      exact h1

end CFSG.RankThree.PartTwo
