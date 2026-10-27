module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem ker_projOf_eq_subgroupOf (H : Subgroup (GL (Fin 3) K)) :
    (projOf H).ker = (StatedScalars (Fin 3) K).subgroupOf H := by
  ext y
  rw [mem_ker_projOf, Subgroup.mem_subgroupOf]

theorem ker_projOf_le_center (H : Subgroup (GL (Fin 3) K)) :
    (projOf H).ker ≤ Subgroup.center H := by
  intro y hy
  rw [mem_ker_projOf] at hy
  rw [Subgroup.mem_center_iff]
  intro z
  refine Subtype.ext ?_
  simpa only [Subgroup.coe_mul] using commute_of_mem_statedScalars hy (z : GL (Fin 3) K)

end CFSG.RankThree.PartTwo.Sec4
