module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovP4
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovP5
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin.H13

theorem map_twoResidual_perm5_cv {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (θ : ↥H →* Equiv.Perm (Fin 5)) (hθ : Function.Surjective θ) :
    ((CFSG.Quasithin.twoResidual H).subgroupOf H).map θ = alternatingGroup (Fin 5) := by
  rw [← CFSG.Quasithin.B6.twoResidual_top_eq_subgroupOf H, CFSG.Quasithin.B6.twoResidual_map_top hθ,
    twoResidual_perm5_cv]

theorem isPerfect_twoResidual_of_perm5_surj_cv {G : Type} [Group G] [Finite G] {H T M : Subgroup G}
    (hmp : CFSG.Quasithin.MinParabolic H T M) (θ : ↥H →* Equiv.Perm (Fin 5))
    (hθ : Function.Surjective θ) :
    Group.IsPerfect ↥(CFSG.Quasithin.twoResidual H) :=
  isPerfect_twoResidual_of_perm5_cv hmp θ hθ (map_twoResidual_perm5_cv H θ hθ)

end CFSG.Quasithin.H13
