module

public import CFSG.Milestones.ASVolI.A3Aut.Case5b

public section

namespace CFSG.ASVolI

open CFSG.Open

section C5Base

variable {G : Type} [Group G]

theorem burnsideAut_c5_center_eq_bot {L T B : Subgroup G} (h : CFSG.Quasithin.A315Hyp L T B)
    {M : Type} [Group M] (e : ↥L ≃* M) : Subgroup.center M = ⊥ := by
  haveI : IsSimpleGroup ↥L := h.simple
  have hLZ : Subgroup.center ↥L = ⊥ := burnsideAut_center_eq_bot h.nonabelian
  rw [eq_bot_iff]
  intro x hx
  have h1 : e.symm x ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hx (e y)
  rw [hLZ, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  calc x = e (e.symm x) := (e.apply_symm_apply x).symm
    _ = 1 := by rw [h1, map_one]

theorem burnsideAut_c5_odd_orderOf {L T B : Subgroup G} (h : CFSG.Quasithin.A315Hyp L T B)
    [L.Normal] {M : Type} [Group M] (e : ↥L ≃* M) {b : G} (hb : b ∈ B) :
    Odd (orderOf (MulAut.congr e (MulAut.conjNormal b : MulAut ↥L))) := by
  haveI := h.sqtk.finite
  rw [MulEquiv.orderOf_eq]
  refine Odd.of_dvd_nat ?_ (orderOf_map_dvd (MulAut.conjNormal : G →* MulAut ↥L) b)
  rw [← Subgroup.orderOf_mk b hb]
  exact Odd.of_dvd_nat h.odd (orderOf_dvd_natCard _)

end C5Base

end CFSG.ASVolI
