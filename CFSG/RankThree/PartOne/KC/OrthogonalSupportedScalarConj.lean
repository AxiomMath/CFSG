module

public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarDefs

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section Conj

variable (F : V ≃+ V) (σ : K ≃+* K) (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v)

include hF in
theorem semilin_symm_smul (c : K) (v : V) : F.symm (c • v) = σ.symm c • F.symm v :=
  F.injective (by rw [AddEquiv.apply_symm_apply, hF, RingEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply])

@[expose] def semilinConjAux (g : V ≃ₗ[K] V) : V ≃ₗ[K] V where
  toFun v := F (g (F.symm v))
  map_add' x y := by simp
  map_smul' c v := by
    simp only [RingHom.id_apply]
    rw [semilin_symm_smul F σ hF, map_smul, hF, RingEquiv.apply_symm_apply]
  invFun v := F (g.symm (F.symm v))
  left_inv v := by simp
  right_inv v := by simp

theorem semilinConjAux_apply (g : V ≃ₗ[K] V) (v : V) :
    semilinConjAux F σ hF g v = F (g (F.symm v)) :=
  rfl

@[expose] def semilinConj : (V ≃ₗ[K] V) →* (V ≃ₗ[K] V) :=
  MonoidHom.mk' (semilinConjAux F σ hF) fun g h => LinearEquiv.ext fun v => by
    simp [semilinConjAux_apply]

theorem semilinConj_apply (g : V ≃ₗ[K] V) (v : V) :
    semilinConj F σ hF g v = F (g (F.symm v)) :=
  rfl

variable {Q : QuadraticForm K V} (μ : K) (hFQ : ∀ v, Q (F v) = μ * σ (Q v))

include hFQ in
theorem semilinConj_mem_orthogonalGroup {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    semilinConj F σ hF g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hg ⊢
  intro v
  rw [semilinConj_apply, hFQ, hg]
  have := hFQ (F.symm v)
  rw [AddEquiv.apply_symm_apply] at this
  exact this.symm

include hFQ in
theorem semilinConj_mem_orthDerived {g : V ≃ₗ[K] V} (hg : g ∈ orthDerived Q) :
    semilinConj F σ hF g ∈ orthDerived Q := by
  have hle : (TauCeti.QuadraticMap.orthogonalGroup Q).map (semilinConj F σ hF) ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨x, hx, rfl⟩
    exact semilinConj_mem_orthogonalGroup F σ hF μ hFQ hx
  have hmap : (orthDerived Q).map (semilinConj F σ hF) ≤ orthDerived Q := by
    rw [orthDerived, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hle hle
  exact hmap ⟨g, hg, rfl⟩

end Conj

theorem semilinConj_prodCongr
    {K : Type*} [Field K] {V E : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup E] [Module K E]
    (F : V ≃+ V) (C : E ≃+ E) (σ : K ≃+* K)
    (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v)
    (hC : ∀ (c : K) (w : E), C (c • w) = σ c • C w)
    (g : V ≃ₗ[K] V) (h : E ≃ₗ[K] E) :
    semilinConj (F.prodCongr C) σ
      (fun c z => Prod.ext (by exact hF c z.1) (by exact hC c z.2))
      (g.prodCongr h) =
    (semilinConj F σ hF g).prodCongr (semilinConj C σ hC h) := by
  apply LinearEquiv.ext
  rintro ⟨v, w⟩
  have hFapp : ∀ (a : V) (b : E), (F.prodCongr C) (a, b) = (F a, C b) :=
    fun a b => rfl
  have hsymm : (F.prodCongr C).symm (v, w) = (F.symm v, C.symm w) := rfl
  rw [semilinConj_apply]
  change (F.prodCongr C) ((g.prodCongr h) ((F.prodCongr C).symm (v, w))) =
    ((semilinConj F σ hF g).prodCongr (semilinConj C σ hC h)) (v, w)
  rw [hsymm,
    show (g.prodCongr h) (F.symm v, C.symm w) =
      (g (F.symm v), h (C.symm w)) from rfl,
    hFapp, LinearEquiv.prodCongr_apply, semilinConj_apply, semilinConj_apply]

section Commute

variable {Q : QuadraticForm K V} {W : Submodule K V} (F : V ≃+ V) (σ : K ≃+* K)
  (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (μ : K) (hFQ : ∀ v, Q (F v) = μ * σ (Q v))

include hF hFQ in
theorem commute_of_projective_centralizes (hperf : Group.IsPerfect ↥(supportedDerived Q W))
    (hle : supportedDerived Q W ≤ orthDerived Q)
    (hκ : ∀ g g' : ↥(orthDerived Q), (g : V ≃ₗ[K] V) ∈ supportedDerived Q W →
      (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
      (QuotientGroup.mk g' : ProjOrthDerived Q) = QuotientGroup.mk g) :
    ∀ g ∈ supportedDerived Q W, ∀ v, F (g v) = g (F v) := by
  set φ := semilinConj F σ hF with hφ
  have hsc : ∀ g : ↥(supportedDerived Q W), (g : V ≃ₗ[K] V)⁻¹ * φ g ∈ scalars K V := by
    intro g
    have hgΩ := hle g.2
    have h1 := hκ ⟨g, hgΩ⟩ ⟨φ g, semilinConj_mem_orthDerived F σ hF μ hFQ hgΩ⟩ g.2
      (fun v => rfl)
    exact Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h1.symm)
  let θ : ↥(supportedDerived Q W) →* ↥(scalars K V) :=
    MonoidHom.mk' (fun g => ⟨(g : V ≃ₗ[K] V)⁻¹ * φ g, hsc g⟩) (by
      intro g h
      apply Subtype.ext
      have hc := commute_of_mem_scalars (hsc g) (h : V ≃ₗ[K] V)⁻¹
      simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
      calc (h : V ≃ₗ[K] V)⁻¹ * (g : V ≃ₗ[K] V)⁻¹ * (φ g * φ h)
          = (h : V ≃ₗ[K] V)⁻¹ * ((g : V ≃ₗ[K] V)⁻¹ * φ g) * φ h := by simp only [mul_assoc]
        _ = ((g : V ≃ₗ[K] V)⁻¹ * φ g) * (h : V ≃ₗ[K] V)⁻¹ * φ h := by rw [← hc]
        _ = ((g : V ≃ₗ[K] V)⁻¹ * φ g) * ((h : V ≃ₗ[K] V)⁻¹ * φ h) := by simp only [mul_assoc])
  have hker : ∀ g : ↥(supportedDerived Q W), θ g = 1 := by
    have hle' : commutator ↥(supportedDerived Q W) ≤ θ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (commute_of_mem_scalars (θ a).2 (θ b))
    intro g
    have htop : commutator ↥(supportedDerived Q W) = ⊤ := hperf.commutator_eq_top
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


section AutCongrBridge

variable {σ : K ≃+* K}
variable [hpair1 : RingHomInvPair (σ : K →+* K) (σ.symm : K →+* K)]
variable [hpair2 : RingHomInvPair (σ.symm : K →+* K) (σ : K →+* K)]

@[expose] noncomputable def semilinLinearEquiv (F : V ≃+ V)
    (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) :
    V ≃ₛₗ[(σ : K →+* K)] V :=
  { toAddEquiv := F, map_smul' := hF }

theorem semilinConj_eq_autCongr (F : V ≃+ V)
    (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) :
    semilinConj F σ hF =
      (LinearEquiv.autCongr (semilinLinearEquiv (σ := σ) F hF)).toMonoidHom := by
  refine MonoidHom.ext fun g => LinearEquiv.ext fun v => ?_
  rw [semilinConj_apply, MulEquiv.coe_toMonoidHom, LinearEquiv.autCongr_apply_apply]
  rfl

end AutCongrBridge

end CFSG.RankThree.PartOne.KCOrthogonal
