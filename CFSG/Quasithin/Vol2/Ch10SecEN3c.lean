module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Setup

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem baum_le_case2
    (he23 : E2.E23Statement) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)) :
    baum T ≤ thompsonJ T ⊔ (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨D⟩ := exists_case2Data he23 h37 h38 h322 hshape h3228 hyp h2 ht htn hJ
  intro s hs
  have hsT : s ∈ T := hs.1
  have hsN : s ∈ Subgroup.normalizer (fsuVM T L I : Set G) := SecA.le_normalizer_fsuVM T L I hsT
  have h1 : convI (SecA.isElemAbelian_fsuVM hyp) ⟨s, hsN⟩ ∈
      autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T) :=
    D.baum_eq ▸ convI_mem_autI _ hs hsN
  obtain ⟨j, hj, hjs⟩ := (mem_autI _).mp h1
  have hjT : (j : G) ∈ T := (iSup₂_le fun _ hA => hA.1 : thompsonJ T ≤ T) hj
  have hc : (j : G)⁻¹ * s ∈ T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) := by
    refine ⟨T.mul_mem (T.inv_mem hjT) hsT, ?_⟩
    have h2 : convI (SecA.isElemAbelian_fsuVM hyp) (j⁻¹ * ⟨s, hsN⟩) = 1 := by
      rw [map_mul, map_inv, hjs, inv_mul_cancel]
    exact (convI_eq_one_iff _ _).mp h2
  have e : s = (j : G) * ((j : G)⁻¹ * s) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hj hc

end CFSG.Quasithin.Vol2.Ch10.SecE
