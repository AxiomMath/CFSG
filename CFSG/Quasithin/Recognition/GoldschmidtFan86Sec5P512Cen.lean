module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P512Base

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan512cen (F : FanTree Γ G) : Fan512cen F := by
  intro _ T z a _ hz hz1 hcore
  have hzz : z * z = 1 := hz.1
  have hα : z ∈ MulAction.stabilizer G (T.line.vert (a + 1)) :=
    MulAction.mem_stabilizer_iff.2 (hcore.2.1 (a + 1) (by omega) (by omega))
  refine ⟨hz1, hzz, hα, fun h hh => ?_⟩
  have hle : Subgroup.closure ((T.line.edgeStab (G := G) a : Set G) ∪
      (T.line.edgeStab (G := G) (a + 1) : Set G)) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff.1 hk]
      exact ((hcore.2.2.1 a le_rfl (by omega)).2 g hg).symm
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff.1 hk]
      exact ((hcore.2.2.1 (a + 1) (by omega) (by omega)).2 g hg).symm
  exact Subgroup.mem_centralizer_singleton_iff.1
    (hle (P512.stab_le_closure_edges F T.line a hh))

end CFSG.Quasithin.Fan86
