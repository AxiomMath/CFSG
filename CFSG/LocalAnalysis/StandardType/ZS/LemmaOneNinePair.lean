module

public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneNineHomology

public section

namespace CFSG.StandardType.ZS

section Field

variable {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U]
  {τ : K} {η₁ η₂ : U ≃ₗ[K] U} {c₁ c₂ : U} {φ₁ φ₂ : Module.Dual K U}

private theorem smul_dual_apply (a : K) (f : Module.Dual K U) (v : U) :
    (a • f) v = a * f v := by
  rw [LinearMap.smul_apply, smul_eq_mul]

private theorem mul_apply_homology (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (v : U) :
    (η₁ * η₂) v = v + φ₁ v • c₁ + φ₂ v • c₂ + (φ₂ v * φ₁ c₂) • c₁ := by
  rw [LinearEquiv.mul_apply, h₂.2 v, h₁.2]
  simp only [map_add, map_smul, smul_eq_mul]
  module

private theorem mul_inv_apply_homology (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (v : U) :
    (η₁ * η₂⁻¹) v =
      v + φ₁ v • c₁ + ((-τ⁻¹) * φ₂ v) • c₂ + (((-τ⁻¹) * φ₂ v) * φ₁ c₂) • c₁ := by
  rw [LinearEquiv.mul_apply, h₂.inv.2 v, h₁.2]
  simp only [map_add, map_smul, LinearMap.smul_apply, smul_eq_mul]
  module

private theorem symm_apply_centre {g : U ≃ₗ[K] U} {c : U} {φ : Module.Dual K U}
    (h : IsHomologyWith τ g c φ) : g.symm c = τ⁻¹ • c := by
  have hτ0 : τ ≠ 0 := h.type_ne_zero
  have hgc : g (g.symm c) = c := LinearEquiv.apply_symm_apply g c
  have hφτ : φ (g.symm c) = τ⁻¹ * φ c := by
    have hφ : φ (g (g.symm c)) = τ * φ (g.symm c) := by
      rw [h.2 (g.symm c), map_add, map_smul, h.1, smul_eq_mul]
      ring
    rw [hgc] at hφ
    rw [hφ, ← mul_assoc, inv_mul_cancel₀ hτ0, one_mul]
  have hrec : g.symm c = c - φ (g.symm c) • c := by
    have h := h.2 (g.symm c)
    rw [hgc] at h
    exact eq_sub_iff_add_eq.mpr h.symm
  have hcoef : (1 : K) - τ⁻¹ * (τ - 1) = τ⁻¹ := by
    field_simp
    ring
  rw [hrec, hφτ, h.1]
  nth_rewrite 1 [← one_smul K c]
  rw [← sub_smul, hcoef]

private theorem eq_of_homology_eq {ψ : Module.Dual K U} {g : U ≃ₗ[K] U} {c : U}
    {φ : Module.Dual K U} (h : IsHomologyWith τ g c φ) (h' : IsHomologyWith τ g c ψ)
    (hτ : τ ≠ 1) : φ = ψ := by
  have hc : c ≠ 0 := h.centre_ne_zero hτ
  ext v
  have heq : φ v • c = ψ v • c := by
    have h1 := h.2 v
    have h2 := (h').2 v
    rw [h1] at h2
    exact add_left_cancel h2
  have : φ v - ψ v = 0 := by
    rcases smul_eq_zero.mp (show (φ v - ψ v) • c = 0 by rw [sub_smul, heq, sub_self]) with h | h
    · exact h
    · exact absurd h hc
  exact sub_eq_zero.mp this

private theorem exists_smul_eq_of_ker_le_ker {f h : Module.Dual K U} {x : U} {t : K}
    (hx : f x = t) (ht : t ≠ 0) (hker : LinearMap.ker f ≤ LinearMap.ker h) :
    ∃ μ : K, h = μ • f := by
  refine ⟨h x * t⁻¹, ?_⟩
  have hfx : f x ≠ 0 := by rw [hx]; exact ht
  ext v
  change h v = (h x * t⁻¹) * f v
  have hv : v ∈ Submodule.span K {x} ⊔ LinearMap.ker f := by
    rw [LinearMap.span_singleton_sup_ker_eq_top f hfx]
    exact Submodule.mem_top
  rcases Submodule.mem_sup.mp hv with ⟨a, ha, b, hb, hab⟩
  rw [Submodule.mem_span_singleton] at ha
  obtain ⟨s, rfl⟩ := ha
  have hb' : h b = 0 := by simpa using hker hb
  have hfb : f b = 0 := by simpa using hb
  rw [← hab]
  have hgv : h (s • x + b) = s * h x := by
    rw [map_add, map_smul, hb', add_zero, smul_eq_mul]
  have hfv : f (s • x + b) = s * t := by
    rw [map_add, map_smul, hfb, add_zero, hx, smul_eq_mul]
  rw [hgv, hfv]
  field_simp

theorem isTransvectionLin_mul_inv_of_mem_span (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (hτ : τ ≠ 1) (hc : c₂ ∈ Submodule.span K {c₁})
    (hne : η₁ ≠ η₂) : QTwoLin.IsTransvectionLin (η₁ * η₂⁻¹) := by
  obtain ⟨ν, hν⟩ := Submodule.mem_span_singleton.mp hc
  have hc1ne : c₁ ≠ 0 := h₁.centre_ne_zero hτ
  have hτ0 : τ ≠ 0 := h₁.type_ne_zero
  have hνφ : ν * φ₂ c₁ = τ - 1 := by
    rw [← smul_eq_mul, ← map_smul, hν]
    exact h₂.1
  have hψne : φ₁ - ν • φ₂ ≠ 0 := by
    intro h0
    apply hne
    have hφ : φ₁ = ν • φ₂ := sub_eq_zero.mp h0
    ext v
    rw [h₁.2 v, h₂.2 v, ← hν, hφ]
    simp only [LinearMap.smul_apply, smul_smul, smul_eq_mul]
    module
  refine ⟨c₁, φ₁ - ν • φ₂, hc1ne, hψne, ?_, ?_⟩
  · rw [LinearMap.sub_apply, LinearMap.smul_apply, h₁.1, smul_eq_mul, hνφ, sub_self]
  · intro v
    rw [mul_inv_apply_homology h₁ h₂ v, ← hν]
    simp only [map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_smul, smul_eq_mul,
      neg_mul, h₁.1]
    have hcoef : φ₁ v + (-τ⁻¹ * φ₂ v) * ν + (-τ⁻¹ * φ₂ v) * (ν * (τ - 1)) =
        φ₁ v - ν * φ₂ v := by
      field_simp
      ring
    rw [← hcoef]
    module

theorem isTransvectionLin_mul_inv_of_ker_le (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (hτ : τ ≠ 1) (hker : LinearMap.ker φ₁ ≤ LinearMap.ker φ₂)
    (hne : η₁ ≠ η₂) : QTwoLin.IsTransvectionLin (η₁ * η₂⁻¹) := by
  obtain ⟨μ, hμ⟩ := exists_smul_eq_of_ker_le_ker h₁.1 (sub_ne_zero.mpr hτ) hker
  have hτ0 : τ ≠ 0 := h₁.type_ne_zero
  have hc1ne : c₁ ≠ 0 := h₁.centre_ne_zero hτ
  have hφ₁ne : φ₁ ≠ 0 := by
    intro h0
    exact sub_ne_zero.mpr hτ (by rw [← h₁.1, h0, LinearMap.zero_apply])
  have huφ : φ₁ (τ⁻¹ • (c₁ - μ • c₂)) = 0 := by
    have hμ₂ : μ * φ₁ c₂ = τ - 1 := by
      rw [← smul_dual_apply μ φ₁ c₂, ← hμ]; exact h₂.1
    rw [map_smul, map_sub, map_smul, h₁.1]
    simp only [smul_eq_mul]
    rw [hμ₂, sub_self, mul_zero]
  have hune : τ⁻¹ • (c₁ - μ • c₂) ≠ 0 := by
    refine smul_ne_zero (inv_ne_zero hτ0) ?_
    intro h0
    apply hne
    have hc : c₁ = μ • c₂ := sub_eq_zero.mp h0
    ext v
    rw [h₁.2 v, h₂.2 v, hc]
    simp only [hμ, LinearMap.smul_apply, smul_smul, smul_eq_mul]
    module
  refine ⟨τ⁻¹ • (c₁ - μ • c₂), φ₁, hune, hφ₁ne, huφ, ?_⟩
  intro v
  rw [mul_inv_apply_homology h₁ h₂ v, hμ]
  simp only [LinearMap.smul_apply, smul_smul, smul_eq_mul, neg_mul]
  have hX : -(τ⁻¹ * (μ * φ₁ v) * φ₁ c₂) = φ₁ v * τ⁻¹ - φ₁ v := by
    have hμ₂ : μ * φ₁ c₂ = τ - 1 := by
      rw [← smul_dual_apply μ φ₁ c₂, ← hμ]; exact h₂.1
    have hτinv : τ⁻¹ * τ = 1 := inv_mul_cancel₀ hτ0
    rw [show τ⁻¹ * (μ * φ₁ v) * φ₁ c₂ = (τ⁻¹ * φ₁ v) * (μ * φ₁ c₂) by ring, hμ₂]
    linear_combination (-(φ₁ v)) * hτinv
  rw [hX]
  module

theorem isTransvectionLin_commutator_of_apply_eq_zero (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (hτ : τ ≠ 1) (h12 : φ₁ c₂ = 0) (h21 : φ₂ c₁ ≠ 0) :
    QTwoLin.IsTransvectionLin (η₁ * η₂ * η₁⁻¹ * η₂⁻¹) := by
  have hτ0 : τ ≠ 0 := h₁.type_ne_zero
  have hη₁c₂ : η₁ c₂ = c₂ := by rw [h₁.2 c₂, h12, zero_smul, add_zero]
  have hconj : IsHomologyWith τ (η₁ * η₂ * η₁⁻¹) c₂
      (φ₂ ∘ₗ (η₁.symm : U →ₗ[K] U)) := by
    have h := h₂.conj η₁
    rwa [hη₁c₂] at h
  have hne : η₁ * η₂ * η₁⁻¹ ≠ η₂ := by
    intro heq
    rw [heq] at hconj
    have hfun : (φ₂ ∘ₗ (η₁.symm : U →ₗ[K] U)) = φ₂ := eq_of_homology_eq hconj h₂ hτ
    have hval : (φ₂ ∘ₗ (η₁.symm : U →ₗ[K] U)) c₁ = τ⁻¹ * φ₂ c₁ := by
      rw [LinearMap.comp_apply]
      change φ₂ (η₁.symm c₁) = τ⁻¹ * φ₂ c₁
      rw [symm_apply_centre h₁, map_smul, smul_eq_mul]
    have hcontra : τ⁻¹ * φ₂ c₁ = φ₂ c₁ := by
      rw [← hval, hfun]
    have hτinv : τ⁻¹ = 1 := by
      have hz : (τ⁻¹ - 1) * φ₂ c₁ = 0 := by
        rw [sub_mul, one_mul, hcontra, sub_self]
      rcases mul_eq_zero.mp hz with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h h21
    have hτ1 : τ = 1 := by
      have h' : τ * τ⁻¹ = τ * 1 := by rw [hτinv]
      rw [mul_inv_cancel₀ hτ0, mul_one] at h'
      exact h'.symm
    exact hτ hτ1
  exact isTransvectionLin_mul_inv_of_mem_span hconj h₂ hτ
    (Submodule.mem_span_singleton.mpr ⟨1, one_smul K c₂⟩) hne

theorem commute_of_apply_eq_zero (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (h12 : φ₁ c₂ = 0) (h21 : φ₂ c₁ = 0) :
    η₁ * η₂ = η₂ * η₁ := by
  ext v
  rw [mul_apply_homology h₁ h₂ v, mul_apply_homology h₂ h₁ v, h12, h21]
  simp only [mul_zero, zero_smul, add_zero]
  module

theorem IsHomologyWith.apply_eq_zero_of_commute (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (hτ : τ ≠ 1) (hcomm : η₁ * η₂ = η₂ * η₁)
    (hind : c₂ ∉ Submodule.span K {c₁}) : φ₁ c₂ = 0 := by
  have hc1ne : c₁ ≠ 0 := h₁.centre_ne_zero hτ
  have heig : η₂ (η₁ c₂) = τ • (η₁ c₂) := by
    calc η₂ (η₁ c₂) = (η₂ * η₁) c₂ := (LinearEquiv.mul_apply η₂ η₁ c₂).symm
      _ = (η₁ * η₂) c₂ := by rw [hcomm]
      _ = η₁ (η₂ c₂) := LinearEquiv.mul_apply η₁ η₂ c₂
      _ = η₁ (τ • c₂) := by rw [h₂.apply_centre]
      _ = τ • η₁ c₂ := map_smul η₁ τ c₂
  have hspan : η₁ c₂ ∈ Submodule.span K {c₂} := h₂.mem_span_of_apply_eq_smul hτ heig
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hspan
  by_contra hb
  have hc1 : c₁ ∈ Submodule.span K {c₂} := by
    have h1 : φ₁ c₂ • c₁ = μ • c₂ - c₂ := by
      have h := h₁.2 c₂
      rw [← hμ] at h
      rw [h]
      abel
    rw [← inv_smul_smul₀ hb c₁, h1]
    exact Submodule.smul_mem _ _
      (Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self c₂))
        (Submodule.mem_span_singleton_self c₂))
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hc1
  apply hind
  rw [Submodule.mem_span_singleton]
  have hlamne : lam ≠ 0 := by
    intro h0
    exact hc1ne (by rw [← hlam, h0, zero_smul])
  refine ⟨lam⁻¹, ?_⟩
  rw [← hlam, smul_smul, inv_mul_cancel₀ hlamne, one_smul]

theorem not_commute_of_apply_ne_zero (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (hτ : τ ≠ 1) (h12 : φ₁ c₂ ≠ 0)
    (hind : c₂ ∉ Submodule.span K {c₁}) : η₁ * η₂ ≠ η₂ * η₁ := by
  intro hcomm
  exact h12 (h₁.apply_eq_zero_of_commute h₂ hτ hcomm hind)

private theorem disjoint_span_ker_inf_ker (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (hΔ : (τ - 1) * (τ - 1) - (φ₁ c₂) * (φ₂ c₁) ≠ 0) :
    Disjoint (Submodule.span K {c₁, c₂}) (LinearMap.ker φ₁ ⊓ LinearMap.ker φ₂) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  rw [Submodule.mem_bot]
  rw [Submodule.mem_inf] at hx
  obtain ⟨hxW, hxY⟩ := hx
  rw [Submodule.mem_inf] at hxY
  obtain ⟨hx1, hx2⟩ := hxY
  rw [LinearMap.mem_ker] at hx1 hx2
  rw [Submodule.mem_span_pair] at hxW
  obtain ⟨s, t, hst⟩ := hxW
  have e1 : s * (τ - 1) + t * (φ₁ c₂) = 0 := by
    rw [← hst] at hx1
    simpa [map_add, map_smul, smul_eq_mul, h₁.1] using hx1
  have e2 : s * (φ₂ c₁) + t * (τ - 1) = 0 := by
    rw [← hst] at hx2
    simpa [map_add, map_smul, smul_eq_mul, h₂.1] using hx2
  have hs : s = 0 := by
    have hz : s * ((τ - 1) * (τ - 1) - (φ₁ c₂) * (φ₂ c₁)) = 0 := by
      linear_combination (τ - 1) * e1 - (φ₁ c₂) * e2
    exact (mul_eq_zero.mp hz).resolve_right hΔ
  have ht : t = 0 := by
    have hz : t * ((τ - 1) * (τ - 1) - (φ₁ c₂) * (φ₂ c₁)) = 0 := by
      linear_combination (τ - 1) * e2 - (φ₂ c₁) * e1
    exact (mul_eq_zero.mp hz).resolve_right hΔ
  rw [← hst, hs, ht, zero_smul, zero_smul, add_zero]

theorem isCompl_span_ker_inf_ker (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (hq : φ₁ c₂ * φ₂ c₁ ≠ (τ - 1) ^ 2) :
    IsCompl (Submodule.span K {c₁, c₂}) (LinearMap.ker φ₁ ⊓ LinearMap.ker φ₂) := by
  have hΔ : (τ - 1) * (τ - 1) - (φ₁ c₂) * (φ₂ c₁) ≠ 0 := by
    intro h0
    apply hq
    rw [pow_two]
    linear_combination -h0
  refine ⟨disjoint_span_ker_inf_ker h₁ h₂ hΔ, ?_⟩
  rw [codisjoint_iff_le_sup]
  intro u _
  rw [Submodule.mem_sup]
  let s : K := ((τ - 1) * φ₁ u - (φ₁ c₂) * φ₂ u) *
    ((τ - 1) * (τ - 1) - (φ₁ c₂) * (φ₂ c₁))⁻¹
  let t : K := ((τ - 1) * φ₂ u - (φ₂ c₁) * φ₁ u) *
    ((τ - 1) * (τ - 1) - (φ₁ c₂) * (φ₂ c₁))⁻¹
  refine ⟨s • c₁ + t • c₂, Submodule.mem_span_pair.mpr ⟨s, t, rfl⟩,
    u - (s • c₁ + t • c₂), ?_, by abel⟩
  rw [Submodule.mem_inf]
  constructor
  · rw [LinearMap.mem_ker]
    have hw : φ₁ (s • c₁ + t • c₂) = φ₁ u := by
      dsimp only [s, t]
      rw [map_add, map_smul, map_smul, h₁.1]
      simp only [smul_eq_mul]
      field_simp
      ring
    rw [map_sub, hw, sub_self]
  · rw [LinearMap.mem_ker]
    have hw : φ₂ (s • c₁ + t • c₂) = φ₂ u := by
      dsimp only [s, t]
      rw [map_add, map_smul, map_smul, h₂.1]
      simp only [smul_eq_mul]
      field_simp
      ring
    rw [map_sub, hw, sub_self]

theorem apply_eq_zero_of_apply_eq_zero {H : Subgroup (U ≃ₗ[K] U)}
    (htv : QTwoLin.TransvectionFree H) (hη₁ : η₁ ∈ H) (hη₂ : η₂ ∈ H)
    (h₁ : IsHomologyWith τ η₁ c₁ φ₁) (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (hτ : τ ≠ 1)
    (h12 : φ₁ c₂ = 0) : φ₂ c₁ = 0 := by
  by_contra h21
  exact htv _ (H.mul_mem (H.mul_mem (H.mul_mem hη₁ hη₂) (H.inv_mem hη₁)) (H.inv_mem hη₂))
    (isTransvectionLin_commutator_of_apply_eq_zero h₁ h₂ hτ h12 h21)

end Field

end CFSG.StandardType.ZS

end
