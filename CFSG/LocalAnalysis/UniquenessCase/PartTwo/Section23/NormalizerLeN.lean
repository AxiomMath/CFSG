module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context
public import CFSG.LocalAnalysis.WeakClosure81.Eleven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)

theorem normalizer_le_N_of_isPGroup {C : Subgroup G} (hCne : C ≠ ⊥)
    (hC2 : IsPGroup 2 C) (hLT : c.L ⊔ D.T ≤ Subgroup.normalizer (C : Set G)) :
    Subgroup.normalizer (C : Set G) ≤ c.N := by
  have hloc : IsTwoLocal (Subgroup.normalizer (C : Set G)) := ⟨C, hCne, hC2, rfl⟩
  obtain ⟨M', hM'max, hle⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.exists_isMaxTwoLocalSubgroup_le hloc
  have hM'mem : M' ∈ calMOf (c.L ⊔ D.T) := ⟨hM'max, hLT.trans hle⟩
  have hM' : M' = c.N := by
    rw [c.hN] at hM'mem
    simpa using hM'mem
  exact hle.trans (le_of_eq hM')

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
