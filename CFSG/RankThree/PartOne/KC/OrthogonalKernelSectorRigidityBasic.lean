module

public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarConj

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section Commute

variable {Q : QuadraticForm K V} {D : Subgroup (V ≃ₗ[K] V)} (F : V ≃+ V) (σ : K ≃+* K)
  (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (μ : K) (hFQ : ∀ v, Q (F v) = μ * σ (Q v))

include hF hFQ in
theorem commute_of_projective_centralizes_of_perfect (hperf : Group.IsPerfect ↥D)
    (hle : D ≤ orthDerived Q)
    (hκ : ∀ g g' : ↥(orthDerived Q), (g : V ≃ₗ[K] V) ∈ D →
      (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
      (QuotientGroup.mk g' : ProjOrthDerived Q) = QuotientGroup.mk g) :
    ∀ g ∈ D, ∀ v, F (g v) = g (F v) := by
  set φ := semilinConj F σ hF with hφ
  have hsc : ∀ g : ↥D, (g : V ≃ₗ[K] V)⁻¹ * φ g ∈ scalars K V := by
    intro g
    have hgΩ := hle g.2
    have h1 := hκ ⟨g, hgΩ⟩ ⟨φ g, semilinConj_mem_orthDerived F σ hF μ hFQ hgΩ⟩ g.2
      (fun v => rfl)
    exact Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h1.symm)
  let θ : ↥D →* ↥(scalars K V) :=
    MonoidHom.mk' (fun g => ⟨(g : V ≃ₗ[K] V)⁻¹ * φ g, hsc g⟩) (by
      intro g h
      apply Subtype.ext
      have hc := commute_of_mem_scalars (hsc g) (h : V ≃ₗ[K] V)⁻¹
      simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
      calc (h : V ≃ₗ[K] V)⁻¹ * (g : V ≃ₗ[K] V)⁻¹ * (φ g * φ h)
          = (h : V ≃ₗ[K] V)⁻¹ * ((g : V ≃ₗ[K] V)⁻¹ * φ g) * φ h := by simp only [mul_assoc]
        _ = ((g : V ≃ₗ[K] V)⁻¹ * φ g) * (h : V ≃ₗ[K] V)⁻¹ * φ h := by rw [← hc]
        _ = ((g : V ≃ₗ[K] V)⁻¹ * φ g) * ((h : V ≃ₗ[K] V)⁻¹ * φ h) := by simp only [mul_assoc])
  have hker : ∀ g : ↥D, θ g = 1 := by
    have hle' : commutator ↥D ≤ θ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (commute_of_mem_scalars (θ a).2 (θ b))
    intro g
    have htop : commutator ↥D = ⊤ := hperf.commutator_eq_top
    exact hle' (htop ▸ Subgroup.mem_top g)
  intro g hg w
  have h1 := congrArg Subtype.val (hker ⟨g, hg⟩)
  have h2 : (g : V ≃ₗ[K] V)⁻¹ * φ g = 1 := h1
  have h3 : φ g = g := by
    have := congrArg (g * ·) h2
    simpa using this
  have h4 := LinearEquiv.congr_fun h3 (F w)
  rw [semilinConj_apply, AddEquiv.symm_apply_apply] at h4
  exact h4

end Commute

section Scalars

theorem eq_of_mixing {F : V ≃+ V} {g : V ≃ₗ[K] V} (hcomm : ∀ v, F (g v) = g (F v))
    {S₁ S₂ : Submodule K V} {c₁ c₂ : K} (h₁ : ∀ v ∈ S₁, F v = c₁ • v)
    (h₂ : ∀ v ∈ S₂, F v = c₂ • v) {v s t : V} (hv : v ∈ S₁) (hs : s ∈ S₁) (ht : t ∈ S₂)
    (ht0 : t ≠ 0) (hgv : g v = s + t) : c₁ = c₂ := by
  have h1 : F (g v) = c₁ • s + c₂ • t := by rw [hgv, map_add, h₁ s hs, h₂ t ht]
  have h2 : g (F v) = c₁ • s + c₁ • t := by rw [h₁ v hv, map_smul, hgv, smul_add]
  have h3 : c₂ • t = c₁ • t := add_left_cancel (h1.symm.trans ((hcomm v).trans h2))
  exact ((smul_left_injective K ht0) h3).symm

theorem eq_smul_of_iSup_eq_top_additive {ι : Type*} {S : ι → Submodule K V} (hS : ⨆ i, S i = ⊤)
    {F : V ≃+ V} {c : K} (h : ∀ i, ∀ v ∈ S i, F v = c • v) : ∀ v, F v = c • v := by
  intro v
  have hv : v ∈ ⨆ i, S i := hS ▸ Submodule.mem_top
  refine Submodule.iSup_induction S (motive := fun v => F v = c • v) hv (fun i w hw => h i w hw)
    ?_ (fun a b ha hb => ?_)
  · rw [map_zero, smul_zero]
  · rw [map_add, ha, hb, smul_add]

theorem eq_refl_of_semilinear_scalar {F : V ≃+ V} {σ : K ≃+* K}
    (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) {S : Submodule K V} (hS : S ≠ ⊥) {c₀ : K}
    (hc₀ : c₀ ≠ 0) (h : ∀ v ∈ S, F v = c₀ • v) : σ = RingEquiv.refl K := by
  obtain ⟨v, hvS, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  refine RingEquiv.ext fun c => ?_
  have h1 : F (c • v) = c₀ • c • v := h _ (S.smul_mem c hvS)
  rw [hF, h v hvS, smul_smul, smul_smul] at h1
  have h3 := smul_left_injective K hv0 h1
  exact mul_right_cancel₀ hc₀ (h3.trans (mul_comm c₀ c))

end Scalars

end CFSG.RankThree.PartOne.KCOrthogonal
