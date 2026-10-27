module

public import CFSG.LocalAnalysis.WeakClosure81.W18PackG

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace MinCex183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem relIndex_cases (c : MinCex183 D V₀ V H i) {g : G} (hgK : ¬ vInH V H g ≤ kerMV V H) :
    (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) = 2 ∨
      3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) := by
  have h0 : (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have h1 : (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    exact hgK fun x hx =>
      c.hyp.inf_centralizer_eOmegaZ_le_kerMV ⟨(inf_le_right : vInH V H g ≤ H) hx, h hx⟩
  omega

end MinCex183

end CFSG.LocalAnalysis.WeakClosure81

end
