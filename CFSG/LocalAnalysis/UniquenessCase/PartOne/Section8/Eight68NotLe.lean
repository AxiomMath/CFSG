module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SupDecomposition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem ne_top_map_quotient_of_not_le
    {G : Type} [Group G] {M H Y : Subgroup G}
    (hYH : Y ≤ H) (hYnorm : (Y.subgroupOf H).Normal) (hYM : Y ≤ M)
    (hHnotM : ¬ H ≤ M) :
    ((M ⊓ H).subgroupOf H).map (QuotientGroup.mk' (Y.subgroupOf H)) ≠ ⊤ := by
  intro htop
  apply hHnotM
  intro h hh
  have hmem : QuotientGroup.mk' (Y.subgroupOf H) (⟨h, hh⟩ : ↥H) ∈
      ((M ⊓ H).subgroupOf H).map (QuotientGroup.mk' (Y.subgroupOf H)) := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_map] at hmem
  obtain ⟨m, hm, hmh⟩ := hmem
  have hmM : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hm).1
  have hy : (m : G)⁻¹ * h ∈ Y := by
    have hq := QuotientGroup.eq.mp hmh
    simpa using (Subgroup.mem_subgroupOf.mp hq)
  have hEq : h = (m : G) * ((m : G)⁻¹ * h) := by group
  rw [hEq]
  exact M.mul_mem hmM (hYM hy)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
