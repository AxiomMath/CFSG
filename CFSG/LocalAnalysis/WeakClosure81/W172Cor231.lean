module

public import CFSG.LocalAnalysis.WeakClosure81.W172Index2
public import CFSG.LocalAnalysis.WeakClosure81.W172LiftGeo
public import CFSG.LocalAnalysis.WeakClosure81.W172WeakT

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace MinCex172

variable {D : Data G} {V₀ V H : Subgroup G}

theorem w172_exists_gam183 (c : MinCex172 D V₀ V H) :
    ∃ g : G, Gam183 V H (eOmegaZ H D.T) 1 g ∧ vInH V H g ≤ D.T := by
  obtain ⟨g, hgT, hgK, hm⟩ := c.hyp.w172_exists_conj_inf_le_T
  refine ⟨g, ⟨hm, fun hle => hgK fun x hx => ?_⟩, hgT⟩
  exact c.hyp.inf_centralizer_eOmegaZ_le_kerMV ⟨hx.2, hle hx⟩

theorem w172_mem_M_of_gam183 (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) 1 g) (hgT : vInH V H g ≤ D.T) : g ∈ D.M :=
  c.w172_mem_M_of_relIndex_le_two (c.w172_wClos_le_conj h162 hg hgT)
    (c.w172_relIndex_le_two h162 hg hgT)

theorem w172_gam183_one (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) :
    Gam183 V H (eOmegaZ H D.T) 1 1 := by
  obtain ⟨g, hg, hgT⟩ := c.w172_exists_gam183
  have hgM : g ∈ D.M := c.w172_mem_M_of_gam183 h162 hg hgT
  have hgN : g ∈ Subgroup.normalizer (V : Set G) := by
    rw [c.hyp.setting.normalizer_eq]
    exact hgM
  have hVg : conjSubgroup V g = V := conjSubgroup_eq_iff_mem_normalizer.mpr hgN
  have hVH : V ≤ H := c.hyp.V_le_T.trans c.hyp.hyp171.2.1
  obtain ⟨-, hC⟩ := hg
  rw [hVg] at hC
  refine ⟨?_, ?_⟩
  · rw [conjSubgroup_one, inf_eq_left.2 hVH, E3.mQuot_self]
    exact Nat.zero_le _
  · rw [conjSubgroup_one]
    exact hC

theorem w172_not_le_centralizer (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) :
    ¬ V ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G) := fun hle =>
  (c.w172_gam183_one h162).2 (by rw [conjSubgroup_one]; exact inf_le_left.trans hle)

end MinCex172

end CFSG.LocalAnalysis.WeakClosure81

end
