module

public import CFSG.LocalAnalysis.WeakClosure81.W172Cor231

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace MinCex172

variable {D : Data G} {V₀ V H : Subgroup G}

theorem w172_V_le_H (c : MinCex172 D V₀ V H) : V ≤ H :=
  c.hyp.V_le_T.trans c.hyp.hyp171.2.1

theorem w172_gam183_of_mem (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) {x : G} (hx : x ∈ H) :
    Gam183 V H (eOmegaZ H D.T) 1 x := by
  have hVH : V ≤ H := c.w172_V_le_H
  have hxH : conjSubgroup H x = H :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hx)
  have hxN : x ∈ Subgroup.normalizer (eOmegaZ H D.T : Set G) :=
    Hyp183.normalizer_eOmegaZ H D.T hx
  have hVxH : conjSubgroup V x ≤ H := by
    have := E3.conjSubgroup_mono_left x hVH
    rwa [hxH] at this
  refine ⟨?_, fun hle => ?_⟩
  · rw [inf_eq_left.2 hVxH, E3.mQuot_self]
    exact Nat.zero_le _
  · apply c.w172_not_le_centralizer h162
    have h1 : conjSubgroup V x ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G) :=
      (inf_eq_left.2 hVxH) ▸ hle
    have h2 := E3.conjSubgroup_mono_left x⁻¹ h1
    rw [E3.conjSubgroup_conj_inv, E3.conjSubgroup_centralizer,
      conjSubgroup_eq_iff_mem_normalizer.mpr ((Subgroup.normalizer _).inv_mem hxN)] at h2
    exact h2

theorem w172_mQuot_conj_le_one (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) {x : G}
    (hx : x ∈ H) : E3.mQuot V (conjSubgroup D.M x) ≤ 1 := by
  have hVH : V ≤ H := c.w172_V_le_H
  have hg1 := c.w172_gam183_one h162
  have hm1 := w172_two5 h162 c hg1
  have hv : vInH V H 1 = V := by
    unfold vInH
    rw [conjSubgroup_one, inf_eq_left.2 hVH]
  rw [hv] at hm1
  have hCx : Subgroup.centralizer (eOmegaZ H D.T : Set G) ≤ conjSubgroup D.M x :=
    w172_centralizer_le_conj_M h162 c (c.w172_gam183_of_mem h162 hx)
  rw [← mQuot_inf_left]
  exact (E3.mQuot_mono (inf_le_inf_left V hCx)).trans hm1

theorem w172_mQuot_conj_dual_le_one (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) {x : G}
    (hx : x ∈ H) : E3.mQuot (conjSubgroup V x) D.M ≤ 1 := by
  have h3 := c.w172_mQuot_conj_le_one h162 (H.inv_mem hx)
  have h4 := E3.mQuot_conjSubgroup (conjSubgroup V x) D.M x⁻¹
  rw [E3.conjSubgroup_conj_inv] at h4
  rw [← h4]
  exact h3

theorem w172_V₀_inf_conj_M_ne_bot (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) {x : G}
    (hx : x ∈ H) : V₀ ⊓ conjSubgroup D.M x ≠ ⊥ := by
  have hg1 := c.w172_gam183_one h162
  have hne := w172_inf_ne_bot h162 c hg1
  rw [conjSubgroup_one] at hne
  have hEx : eOmegaZ H D.T ≤ conjSubgroup D.M x :=
    w172_le_conj_M h162 c (c.w172_gam183_of_mem h162 hx)
  intro hbot
  apply hne
  refine eq_bot_iff.2 fun y hy => ?_
  have : y ∈ V₀ ⊓ conjSubgroup D.M x := ⟨hy.2, hEx hy.1⟩
  rwa [hbot] at this

theorem w172_conj_V₀_inf_M_ne_bot (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) {x : G}
    (hx : x ∈ H) : conjSubgroup V₀ x ⊓ D.M ≠ ⊥ := by
  have h5 := c.w172_V₀_inf_conj_M_ne_bot h162 (H.inv_mem hx)
  intro hbot
  apply h5
  have h6 : conjSubgroup (V₀ ⊓ conjSubgroup D.M x⁻¹) x = ⊥ := by
    rw [E3.conjSubgroup_inf, E3.conjSubgroup_inv_conj]
    exact hbot
  rw [← E3.conjSubgroup_conj_inv (V₀ ⊓ conjSubgroup D.M x⁻¹) x, h6, E3.conjSubgroup_bot]

theorem w172_inCalO_one (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) {x : G} (hx : x ∈ H)
    (h1 : ¬ conjSubgroup V x ≤ D.M) (h2 : ¬ V ≤ conjSubgroup D.M x) :
    InCalO 1 D.M V₀ V x :=
  ⟨⟨h1, c.w172_mQuot_conj_le_one h162 hx, fun _ => c.w172_V₀_inf_conj_M_ne_bot h162 hx⟩,
    ⟨h2, c.w172_mQuot_conj_dual_le_one h162 hx,
      fun _ => c.w172_conj_V₀_inf_M_ne_bot h162 hx⟩⟩

end MinCex172

end CFSG.LocalAnalysis.WeakClosure81

end
