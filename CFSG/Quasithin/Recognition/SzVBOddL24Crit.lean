module

public import CFSG.Quasithin.Background.F7

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G}

theorem exists_nData (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) (hinf : G₁ ⊓ G₂ = T)
    (hb : 3 ≤ critDist G₀ G₁ G₂ V) (hodd : Odd (critDist G₀ G₁ G₂ V)) :
    ∃ g : ↥G₀, dist (γ₁ G₀ G₁ G₂) (g • γ₀ G₀ G₁ G₂) + 2 = critDist G₀ G₁ G₂ V ∧
      dist (γ₁ G₀ G₁ G₂) (g • γ₁ G₀ G₁ G₂) + 1 = critDist G₀ G₁ G₂ V ∧
      conjSub (g : G)⁻¹ (conjClosure V G₂) ≤ T ∧
      ⁅⁅conjClosure V G₂, conjSub (g : G)⁻¹ (conjClosure V G₂)⁆,
        conjSub (g : G)⁻¹ (conjClosure V G₂)⁆ = ⊥ ∧
      (∃ y ∈ conjSub (g : G)⁻¹ (conjClosure V G₂), y * y = 1 ∧ y ∉ pCoreOf 2 G₂) ∧
      ⁅conjClosure V G₂, conjSub (g : G)⁻¹ (conjClosure V G₂)⁆ ≤
        conjSub (g : G)⁻¹ (conjClosure V G₂) := by
  obtain ⟨γ, hγ⟩ := exists_isCriticalVertex hyp hV
  have hvt : vtype γ = true := vtype_eq_true_of_odd hyp.gen (by rw [hγ.dist_eq]; exact hodd)
  obtain ⟨⟨γ', hγ', hd'⟩, -⟩ := exists_nbrs_of_geodesic hyp.gen hγ.geodesic (by omega)
  have hadj : (graph G₀ G₁ G₂).Adj γ' γ := hγ'
  obtain ⟨g, ⟨h0, h1⟩ | ⟨h0, h1⟩⟩ := exists_smul_edge hadj
  swap
  · exfalso
    have := vtype_smul g (γ₀ G₀ G₁ G₂)
    rw [h0, vtype_γ₀] at this
    rw [hvt] at this
    exact Bool.noConfusion this
  have hN := hyp.normalizes
  have hW : Vv V (γ₁ G₀ G₁ G₂) = conjClosure V G₂ := Vv_γ₁ hyp.le₂ hN
  have hVγ : Vv V γ = conjSub (g : G) (conjClosure V G₂) := by
    rw [← h1, Vv_smul hN, hW]
  have hst' : stab γ' = conjSub (g : G) G₁ := by rw [← h0, stab_smul, stab_γ₀ hyp.le₁]
  have hst : stab γ = conjSub (g : G) G₂ := by rw [← h1, stab_smul, stab_γ₁ hyp.le₂]
  refine ⟨g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0]
    exact hd'
  · rw [h1]
    have := hγ.geodesic
    omega
  · have h5 := Vv_γ₁_le_pCoreOf_stab_inf hyp hV hγ' hd'
    rw [hW, hst', hst, ← conjSub_inf, hinf] at h5
    have h6 : conjClosure V G₂ ≤ conjSub (g : G) T := h5.trans (pCoreOf_le 2 _)
    rw [conjSub_le_iff, inv_inv]
    exact h6
  · have hquad := (quadratic_Vv_γ₁_Vv hyp hV hγ.geodesic hb hodd).2.2.2
    rw [hVγ, hW] at hquad
    have h7 := congrArg (conjSub (g : G)⁻¹) hquad
    rw [conjSub_bot, ← conjSub_commutator, ← conjSub_commutator, conjSub_conjSub_inv] at h7
    exact h7
  · have hnV : ¬ V ≤ pCoreOf 2 (conjSub (g : G) G₂) := by
      intro hle
      apply hγ.not_le
      rw [← hst] at hle
      exact hle.trans (pCoreOf_stab_le_ballStab_one hyp.toAmalgamHyp _)
    obtain ⟨v, hv, hvn⟩ := IsConcreteLE.not_le_iff_exists.mp hnV
    have hvv : v * v = 1 := by
      have := isElemAbelian_pow_eq_one hyp.elemAbelian hv
      rwa [pow_two] at this
    refine ⟨(g : G)⁻¹ * v * g, ?_, ?_, ?_⟩
    · rw [mem_conjSub, inv_inv]
      have e : (g : G) * ((g : G)⁻¹ * v * g) * (g : G)⁻¹ = v := by group
      rw [e]
      exact le_conjClosure V G₂ hv
    · calc (g : G)⁻¹ * v * g * ((g : G)⁻¹ * v * g) = (g : G)⁻¹ * (v * v) * g := by group
        _ = 1 := by rw [hvv]; group
    · intro hy
      apply hvn
      rw [pCoreOf_conjSub, mem_conjSub]
      exact hy
  · have hc := commutator_Vv_γ₁_Vv_le hyp hV hγ.geodesic (by omega)
    rw [hVγ, hW] at hc
    have h8 := conjSub_mono (g : G)⁻¹ hc
    rw [← conjSub_commutator, conjSub_inf, conjSub_conjSub_inv] at h8
    rw [Subgroup.commutator_comm]
    exact h8.trans inf_le_left

end CFSG.Quasithin.SzVB
