module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggQ2s08k2_mono_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (b : Module.Basis (Fin N) (ZMod 3) V) (w : V ≃ₗ[ZMod 3] V) (xv : V) (i₀ : Fin N)
    (c : ZMod 3) (σ : Equiv.Perm (Fin N)) (ε : Fin N → ZMod 3)
    (hxv : xv = c • b i₀) (hw : ∀ i, w (b i) = ε i • b (σ i)) :
    w xv = (c * ε i₀) • b (σ i₀) := by
  rw [hxv, map_smul, hw, smul_smul]

theorem ggQ2s08core_frame_vector {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (b : Module.Basis (Fin N) (ZMod 3) V) (R W : Subgroup (V ≃ₗ[ZMod 3] V))
    (hRm : ∀ a ∈ R, GGQ2S08Mono b a) (hWR : W ≤ R) (xv : V) (i₀ : Fin N)
    (hxi : ∀ i, i ≠ i₀ → b.repr xv i = 0) (hx : xv ≠ 0)
    (htrans : ∀ i j, i ≠ i₀ → j ≠ i₀ → ∃ w ∈ W, ∃ ε : ZMod 3, ε ≠ 0 ∧ w (b i) = ε • b j)
    (r : V ≃ₗ[ZMod 3] V) (hrR : r ∈ R) (hrx : ¬ ∃ c : ZMod 3, r xv = c • xv) :
    GGQ2S08M0 R W r xv = R := by
  have hsupp : (b.repr xv).support ⊆ {i₀} := by
    intro i hi
    rw [Finset.mem_singleton]
    by_contra h
    exact (Finsupp.mem_support_iff.mp hi) (hxi i h)
  have hxv : xv = b.repr xv i₀ • b i₀ :=
    Module.Basis.eq_smul_of_repr_support_subset_singleton b hsupp
  have hc0 : b.repr xv i₀ ≠ 0 := by
    intro h
    apply hx
    rw [hxv, h, zero_smul]
  have hCR : GGQ2S08M0 R W r xv ≤ R := by
    rw [GGQ2S08M0]
    refine (Subgroup.closure_le R).mpr ?_
    rintro a (ha | ha)
    · rcases ha with ha | ha
      · exact hWR ha
      · rw [Set.mem_singleton_iff] at ha
        exact ha ▸ hrR
    · exact ha.1
  refine le_antisymm hCR ?_
  intro g hg
  obtain ⟨σ, ε, hε, hgε⟩ := hRm g hg
  by_cases hσ : σ i₀ = i₀
  · have hstab : g xv = ε i₀ • xv := by
      have h1 : g xv = (b.repr xv i₀ * ε i₀) • b (σ i₀) :=
        ggQ2s08k2_mono_apply b g xv i₀ (b.repr xv i₀) σ ε hxv hgε
      rw [h1, hσ]
      conv_rhs => rw [hxv]
      rw [smul_smul, mul_comm (b.repr xv i₀) (ε i₀)]
    exact Subgroup.subset_closure (Or.inr ⟨hg, ε i₀, hε i₀, hstab⟩)
  · obtain ⟨σ', ε', hε', hrε⟩ := hRm r hrR
    have hσ' : σ' i₀ ≠ i₀ := by
      intro h
      apply hrx
      refine ⟨ε' i₀, ?_⟩
      have h1 : r xv = (b.repr xv i₀ * ε' i₀) • b (σ' i₀) :=
        ggQ2s08k2_mono_apply b r xv i₀ (b.repr xv i₀) σ' ε' hxv hrε
      rw [h1, h]
      conv_rhs => rw [hxv]
      rw [smul_smul, mul_comm (b.repr xv i₀) (ε' i₀)]
    obtain ⟨w, hwW, ε'', hε'', hw⟩ := htrans (σ' i₀) (σ i₀) hσ' hσ
    have hrC : r ∈ GGQ2S08M0 R W r xv :=
      Subgroup.subset_closure (Or.inl (Or.inr rfl))
    have hwC : w ∈ GGQ2S08M0 R W r xv :=
      Subgroup.subset_closure (Or.inl (Or.inl hwW))
    have hmC : w * r ∈ GGQ2S08M0 R W r xv := mul_mem hwC hrC
    have hmR : w * r ∈ R := hCR hmC
    have hm_bi : (w * r) (b i₀) = (ε' i₀ * ε'') • b (σ i₀) := by
      rw [LinearEquiv.mul_apply, hrε i₀, map_smul, hw, smul_smul]
    have hs : ε' i₀ * ε'' ≠ 0 := mul_ne_zero (hε' i₀) hε''
    have hsymm : (w * r).symm (b (σ i₀)) = (ε' i₀ * ε'')⁻¹ • b i₀ := by
      have hb : b (σ i₀) = (ε' i₀ * ε'')⁻¹ • (w * r) (b i₀) := by
        rw [hm_bi, smul_smul, inv_mul_cancel₀ hs, one_smul]
      rw [hb, map_smul, LinearEquiv.symm_apply_apply]
    have ha_bi : ((w * r)⁻¹ * g) (b i₀) = (ε i₀ * (ε' i₀ * ε'')⁻¹) • b i₀ := by
      rw [LinearEquiv.mul_apply, LinearEquiv.coe_inv, hgε i₀, map_smul, hsymm, smul_smul]
    have ha_xv : ((w * r)⁻¹ * g) xv = (ε i₀ * (ε' i₀ * ε'')⁻¹) • xv := by
      conv_lhs => rw [hxv]
      rw [map_smul, ha_bi, smul_smul]
      conv_rhs => rw [hxv]
      rw [smul_smul, mul_comm (b.repr xv i₀) (ε i₀ * (ε' i₀ * ε'')⁻¹)]
    have haR : (w * r)⁻¹ * g ∈ R := mul_mem (inv_mem hmR) hg
    have ha_ls : (w * r)⁻¹ * g ∈ GGQ2S08LineStab R xv :=
      ⟨haR, ε i₀ * (ε' i₀ * ε'')⁻¹, mul_ne_zero (hε i₀) (inv_ne_zero hs), ha_xv⟩
    have haC : (w * r)⁻¹ * g ∈ GGQ2S08M0 R W r xv :=
      Subgroup.subset_closure (Or.inr ha_ls)
    exact mul_inv_cancel_left (w * r) g ▸ mul_mem hmC haC

end CFSG.StandardType

end
