module

public import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.LocalAnalysis

open Subgroup

theorem Ccomponent_proper_subnormal_solvable {G : Type*} [Group G] [Finite G]
    {L U : Subgroup G} (hL : IsCComponent L) (hUL : U < L) (hU : (U.subgroupOf L).IsSubnormal) :
    Group.IsSolvable U := by
  obtain ⟨-, -, hLs, hLmin⟩ := hL
  obtain ⟨-, hchar, hperf, -, -, hsolv⟩ := perfect_residual_characterization (G := U)
  rw [← hsolv]
  by_contra hne
  set D : Subgroup G := (perfectResidual U).map U.subtype with hD
  have hDU : D ≤ U := map_subtype_le _
  have hUs : U.IsSubnormal := hU.trans hUL.le hLs
  have hDs : D.IsSubnormal := by
    have : (perfectResidual U).Normal := normal_of_characteristic _
    exact this.isSubnormal.trans' hUs
  have hD1 : D ≠ ⊥ := fun h => hne ((map_eq_bot_iff_of_injective _ U.subtype_injective).mp h)
  have hDp : ⁅D, D⁆ = D := by
    rw [hD, ← map_commutator, (Subgroup.isPerfect_iff).mp hperf]
  exact hLmin D (lt_of_le_of_lt hDU hUL) hD1 hDp hDs

end CFSG.LocalAnalysis
