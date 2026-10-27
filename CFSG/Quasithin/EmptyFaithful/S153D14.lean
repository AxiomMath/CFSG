module

public import CFSG.Quasithin.EmptyFaithful.S153DDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I : Subgroup G} {t : G}

theorem lemma_15_3_14_one (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (hF : Facts15311 T M V₁ Yp I) :
    VZ T M ≤ centerOf (R153 T V₁ Yp) := by
  have hV := h.hyp.elemAbelian
  have hVT : VZ T M ≤ T := h.hyp.VZ_le_T
  have hVc : ∀ v ∈ VZ T M, ∀ w ∈ VZ T M, v * w = w * v := fun v hv w hw =>
    B2F.isElemAbelian_comm hV hv hw
  have hVC : VZ T M ≤ Subgroup.centralizer (VZ T M : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => (hVc v hv w hw).symm
  intro v hv
  refine ⟨?_, ?_⟩
  · rw [hF.R_eq]
    exact ⟨hVT hv, hVC hv⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun r hr => ?_
    rw [hF.R_eq] at hr
    exact (Subgroup.mem_centralizer_iff.mp hr.2 v hv).symm

end S153D

end CFSG.Quasithin
