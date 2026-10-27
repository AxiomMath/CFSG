module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

theorem isEmpty_mulEquiv_alternatingGroup_six_of_map {U X : Type} [Group U] [Group X]
    (ψ : U →* X) (hψ : ψ.ker ≤ Subgroup.center U) (J' : Subgroup U)
    (h : IsEmpty (↥(J'.map ψ) ≃* alternatingGroup (Fin 6))) :
    IsEmpty (↥J' ≃* alternatingGroup (Fin 6)) := by
  refine ⟨fun e => h.false ?_⟩
  have hZ : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hinj : Function.Injective (ψ.subgroupMap J') := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : ψ x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxc : (x : U) ∈ Subgroup.center U := hψ (MonoidHom.mem_ker.mpr hx1)
    have hex : e x ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro a
      obtain ⟨y, rfl⟩ := e.surjective a
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (Subgroup.mem_center_iff.mp hxc y))
    rw [hZ, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hex
    rw [Subgroup.mem_bot]
    exact hex
  exact (MulEquiv.ofBijective (ψ.subgroupMap J') ⟨hinj, ψ.subgroupMap_surjective J'⟩).symm.trans e

end CFSG.StandardType.ClassicalPosition
