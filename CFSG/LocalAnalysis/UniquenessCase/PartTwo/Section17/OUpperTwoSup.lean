module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIX

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.ClassicalInvolution.Asc77.T3CII

variable {G : Type} [Group G] [Finite G]

theorem oUpperTwo_sup_eq_of_normal {X T : Subgroup G}
    (hXN : (X.subgroupOf (X ⊔ T)).Normal) (hT2 : IsPGroup 2 T) :
    oUpperTwo (X ⊔ T) = oUpperTwo X := by
  have hXnorm : X ⊔ T ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hXN
  have hTnorm : T ≤ Subgroup.normalizer (X : Set G) := le_sup_right.trans hXnorm
  apply le_antisymm
  · rw [oUpperTwo_eq_closure, oUpperTwo_eq_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyH, hyodd⟩
    exact Subgroup.subset_closure
      ⟨mem_of_odd_orderOf_of_mem_sup hT2 hTnorm hyH hyodd, hyodd⟩
  · rw [oUpperTwo_eq_closure, oUpperTwo_eq_closure]
    exact Subgroup.closure_mono fun y hy => ⟨(le_sup_left : X ≤ X ⊔ T) hy.1, hy.2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
