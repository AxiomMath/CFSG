module

public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneAlgebra
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitCoordinates

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

section Determinant

variable {K : Type*} [Field K]

theorem determinantForm_nondegenerate : (polarBilin (determinantForm K)).Nondegenerate := by
  refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun X hX => ?_
  have h00 := hX (Matrix.of ![![0, 0], ![0, 1]])
  have h11 := hX (Matrix.of ![![1, 0], ![0, 0]])
  have h01 := hX (Matrix.of ![![0, 0], ![1, 0]])
  have h10 := hX (Matrix.of ![![0, 1], ![0, 0]])
  simp only [determinantForm_polar, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val'] at h00 h11 h01 h10
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

theorem nondegenerate_polarBilin_of_isometryEquiv_univ {V V' : Type*} [AddCommGroup V]
    [Module K V] [AddCommGroup V'] [Module K V'] {Q : QuadraticForm K V}
    {Q' : QuadraticForm K V'} (e : Q.IsometryEquiv Q') (hQ : (polarBilin Q).Nondegenerate) :
    (polarBilin Q').Nondegenerate := by
  refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun x hx => ?_
  have key : ∀ a b, polar Q a b = polar Q' (e a) (e b) := fun a b => by
    simp only [polar, ← map_add, e.map_app]
  have h : e.symm x = 0 := hQ.1 _ fun y => by
    rw [polarBilin_apply_apply, key, e.apply_symm_apply]
    exact hx (e y)
  simpa using congrArg e h

end Determinant

section Planes

variable {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E]
  {V : Type*} [AddCommGroup V] [Module K V]

structure NormPlanes (D : QuadData K E) (Q : QuadraticForm K V) (U₁ U₂ : Submodule K V)
    (φ₁ : E →ₗ[K] U₁) (φ₂ : E →ₗ[K] U₂) : Prop where
  finrank₁ : finrank K U₁ = 2
  finrank₂ : finrank K U₂ = 2
  reg₁ : ∀ v ∈ U₁, (∀ x ∈ U₁, polar Q x v = 0) → v = 0
  orth : ∀ x ∈ U₁, ∀ y ∈ U₂, polar Q x y = 0
  norm₁ : ∀ z, Q (φ₁ z : V) = D.Nm z
  norm₂ : ∀ z, Q (φ₂ z : V) = D.Nm z

variable {D : QuadData K E} {Q : QuadraticForm K V} {U₁ U₂ : Submodule K V}
  {φ₁ : E →ₗ[K] U₁} {φ₂ : E →ₗ[K] U₂}

@[expose] def pairMap (φ₁ : E →ₗ[K] U₁) (φ₂ : E →ₗ[K] U₂) : (E × E) →ₗ[K] V :=
  (U₁.subtype ∘ₗ φ₁) ∘ₗ LinearMap.fst K E E + (U₂.subtype ∘ₗ φ₂) ∘ₗ LinearMap.snd K E E

theorem pairMap_apply (φ₁ : E →ₗ[K] U₁) (φ₂ : E →ₗ[K] U₂) (z₁ z₂ : E) :
    pairMap φ₁ φ₂ (z₁, z₂) = (φ₁ z₁ : V) + (φ₂ z₂ : V) := rfl

theorem pairMap_mem (φ₁ : E →ₗ[K] U₁) (φ₂ : E →ₗ[K] U₂) (w : E × E) :
    pairMap φ₁ φ₂ w ∈ U₁ ⊔ U₂ :=
  Submodule.add_mem_sup (φ₁ w.1).2 (φ₂ w.2).2

theorem _root_.CFSG.RankThree.PartOne.KCOrthogonal.QuadData.eq_zero_of_Nm_eq_zero
    (D : QuadData K E) {z : E} (hz : D.Nm z = 0) : z = 0 := by
  refine D.Nm_eq_zero ?_
  rw [← D.algebraMap_Nm, hz, map_zero]

namespace NormPlanes

variable (h : NormPlanes D Q U₁ U₂ φ₁ φ₂)

include h

theorem φ₁_injective : Function.Injective φ₁ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  refine D.eq_zero_of_Nm_eq_zero ?_
  rw [← h.norm₁, hz]
  simp

theorem φ₂_injective : Function.Injective φ₂ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  refine D.eq_zero_of_Nm_eq_zero ?_
  rw [← h.norm₂, hz]
  simp

theorem φ₁_surjective : Function.Surjective φ₁ := by
  have : Module.Finite K E := Module.Finite.of_basis D.basis
  have : Module.Finite K U₁ := Module.finite_of_finrank_pos (by rw [h.finrank₁]; norm_num)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [D.finrank_eq_two, h.finrank₁])).mp h.φ₁_injective

theorem φ₂_surjective : Function.Surjective φ₂ := by
  have : Module.Finite K E := Module.Finite.of_basis D.basis
  have : Module.Finite K U₂ := Module.finite_of_finrank_pos (by rw [h.finrank₂]; norm_num)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [D.finrank_eq_two, h.finrank₂])).mp h.φ₂_injective

theorem inf_eq_bot : U₁ ⊓ U₂ = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  exact h.reg₁ v hv.1 fun x hx => h.orth x hx v hv.2

theorem pairMap_injective : Function.Injective (pairMap φ₁ φ₂) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨z₁, z₂⟩ hz
  rw [pairMap_apply] at hz
  have h1 : (φ₁ z₁ : V) ∈ U₁ ⊓ U₂ := by
    refine ⟨(φ₁ z₁).2, ?_⟩
    have : (φ₁ z₁ : V) = -(φ₂ z₂ : V) := eq_neg_of_add_eq_zero_left hz
    rw [this]
    exact U₂.neg_mem (φ₂ z₂).2
  have h2 : (φ₁ z₁ : V) = 0 := by
    have := h1
    rw [h.inf_eq_bot, Submodule.mem_bot] at this
    exact this
  have h3 : φ₁ z₁ = 0 := Subtype.ext h2
  have h4 : z₁ = 0 := h.φ₁_injective (by rw [h3, map_zero])
  have hz' : (φ₂ z₂ : V) = 0 := by simpa [h4] using hz
  have h5 : φ₂ z₂ = 0 := Subtype.ext hz'
  have h6 : z₂ = 0 := h.φ₂_injective (by rw [h5, map_zero])
  rw [h4, h6]
  rfl

theorem range_pairMap : LinearMap.range (pairMap φ₁ φ₂) = U₁ ⊔ U₂ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, rfl⟩
    exact pairMap_mem φ₁ φ₂ w
  · intro v hv
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨z₁, hz₁⟩ := h.φ₁_surjective ⟨u₁, hu₁⟩
    obtain ⟨z₂, hz₂⟩ := h.φ₂_surjective ⟨u₂, hu₂⟩
    exact ⟨(z₁, z₂), by rw [pairMap_apply, hz₁, hz₂]⟩

theorem Q_pairMap (w : E × E) : Q (pairMap φ₁ φ₂ w) = D.Nm w.1 + D.Nm w.2 := by
  rw [pairMap_apply, QuadraticMap.map_add Q (φ₁ w.1 : V) (φ₂ w.2 : V), h.norm₁, h.norm₂,
    h.orth _ (φ₁ w.1).2 _ (φ₂ w.2).2, add_zero]

@[expose] noncomputable def pairEquiv : (E × E) ≃ₗ[K] ↥(U₁ ⊔ U₂) :=
  (LinearEquiv.ofInjective (pairMap φ₁ φ₂) h.pairMap_injective).trans
    (LinearEquiv.ofEq _ _ h.range_pairMap)

theorem coe_pairEquiv (w : E × E) : (h.pairEquiv w : V) = pairMap φ₁ φ₂ w := rfl

theorem finrank_sup : finrank K ↥(U₁ ⊔ U₂) = 4 := by
  have : Module.Finite K E := Module.Finite.of_basis D.basis
  rw [← h.pairEquiv.finrank_eq, Module.finrank_prod, D.finrank_eq_two]

@[expose] noncomputable def normPlaneIsometry {c : E} (hc : c ≠ 0) (hNc : D.Nm c = -1) :
    (Q.comp (U₁ ⊔ U₂).subtype).IsometryEquiv (determinantForm K) where
  toLinearEquiv := h.pairEquiv.symm.trans (D.phiEquiv hc)
  map_app' := fun r => by
    obtain ⟨w, rfl⟩ := h.pairEquiv.surjective r
    change determinantForm K (D.phiEquiv hc (h.pairEquiv.symm (h.pairEquiv w))) = Q (h.pairEquiv w)
    rw [LinearEquiv.symm_apply_apply, determinantForm_apply, D.phiEquiv_apply, D.det_phi,
      D.Nm_mul, hNc, coe_pairEquiv, h.Q_pairMap]
    ring

theorem normPlaneIsometry_apply {c : E} (hc : c ≠ 0) (hNc : D.Nm c = -1) (r : ↥(U₁ ⊔ U₂)) :
    h.normPlaneIsometry hc hNc r = D.phi c (h.pairEquiv.symm r) := rfl

theorem nondegenerate_sup {c : E} (hc : c ≠ 0) (hNc : D.Nm c = -1) :
    (polarBilin (Q.comp (U₁ ⊔ U₂).subtype)).Nondegenerate :=
  nondegenerate_polarBilin_of_isometryEquiv_univ (h.normPlaneIsometry hc hNc).symm
    determinantForm_nondegenerate

omit h in
theorem act_pairMap {x : V ≃ₗ[K] V} {μ₁ μ₂ : E}
    (hx₁ : ∀ z, x (φ₁ z : V) = (φ₁ (μ₁ * z) : V))
    (hx₂ : ∀ z, x (φ₂ z : V) = (φ₂ (μ₂ * z) : V)) (w : E × E) :
    x (pairMap φ₁ φ₂ w) = pairMap φ₁ φ₂ (μ₁ * w.1, μ₂ * w.2) := by
  rw [pairMap_apply, map_add, hx₁, hx₂]
  rfl

omit h in
theorem symm_act_pairMap {x : V ≃ₗ[K] V} {μ₁ μ₂ : E} (hμ₁ : μ₁ ≠ 0) (hμ₂ : μ₂ ≠ 0)
    (hx₁ : ∀ z, x (φ₁ z : V) = (φ₁ (μ₁ * z) : V))
    (hx₂ : ∀ z, x (φ₂ z : V) = (φ₂ (μ₂ * z) : V)) (w : E × E) :
    x.symm (pairMap φ₁ φ₂ w) = pairMap φ₁ φ₂ (μ₁⁻¹ * w.1, μ₂⁻¹ * w.2) := by
  rw [LinearEquiv.symm_apply_eq, act_pairMap hx₁ hx₂, mul_inv_cancel_left₀ hμ₁,
    mul_inv_cancel_left₀ hμ₂]

theorem act_mem_sup {x : V ≃ₗ[K] V} {μ₁ μ₂ : E} (hx₁ : ∀ z, x (φ₁ z : V) = (φ₁ (μ₁ * z) : V))
    (hx₂ : ∀ z, x (φ₂ z : V) = (φ₂ (μ₂ * z) : V)) {r : V} (hr : r ∈ U₁ ⊔ U₂) :
    x r ∈ U₁ ⊔ U₂ := by
  rw [← h.range_pairMap] at hr
  obtain ⟨w, rfl⟩ := hr
  rw [act_pairMap hx₁ hx₂]
  exact pairMap_mem _ _ _

theorem symm_act_mem_sup {x : V ≃ₗ[K] V} {μ₁ μ₂ : E} (hμ₁ : μ₁ ≠ 0) (hμ₂ : μ₂ ≠ 0)
    (hx₁ : ∀ z, x (φ₁ z : V) = (φ₁ (μ₁ * z) : V))
    (hx₂ : ∀ z, x (φ₂ z : V) = (φ₂ (μ₂ * z) : V)) {r : V} (hr : r ∈ U₁ ⊔ U₂) :
    x.symm r ∈ U₁ ⊔ U₂ := by
  rw [← h.range_pairMap] at hr
  obtain ⟨w, rfl⟩ := hr
  rw [symm_act_pairMap hμ₁ hμ₂ hx₁ hx₂]
  exact pairMap_mem _ _ _

theorem act_perp {x : V ≃ₗ[K] V} (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {μ₁ μ₂ : E}
    (hμ₁ : μ₁ ≠ 0) (hμ₂ : μ₂ ≠ 0) (hx₁ : ∀ z, x (φ₁ z : V) = (φ₁ (μ₁ * z) : V))
    (hx₂ : ∀ z, x (φ₂ z : V) = (φ₂ (μ₂ * z) : V)) {w : V}
    (hw : ∀ r ∈ U₁ ⊔ U₂, polar Q r w = 0) : ∀ r ∈ U₁ ⊔ U₂, polar Q r (x w) = 0 := by
  intro r hr
  have h1 := h.symm_act_mem_sup hμ₁ hμ₂ hx₁ hx₂ hr
  have h2 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hxO (x.symm r) w
  rw [LinearEquiv.apply_symm_apply] at h2
  rw [h2]
  exact hw _ h1

theorem psi_act {c : E} (hc : c ≠ 0) (hNc : D.Nm c = -1) {x : V ≃ₗ[K] V} {μ₁ μ₂ : E}
    (hx₁ : ∀ z, x (φ₁ z : V) = (φ₁ (μ₁ * z) : V))
    (hx₂ : ∀ z, x (φ₂ z : V) = (φ₂ (μ₂ * z) : V)) (r : ↥(U₁ ⊔ U₂)) :
    ∃ hr : x (r : V) ∈ U₁ ⊔ U₂, h.normPlaneIsometry hc hNc ⟨x r, hr⟩ =
      D.phi c (μ₁ * (h.pairEquiv.symm r).1, μ₂ * (h.pairEquiv.symm r).2) := by
  obtain ⟨w, rfl⟩ := h.pairEquiv.surjective r
  have hmem : x (h.pairEquiv w : V) ∈ U₁ ⊔ U₂ := h.act_mem_sup hx₁ hx₂ (h.pairEquiv w).2
  refine ⟨hmem, ?_⟩
  have : (⟨x (h.pairEquiv w : V), hmem⟩ : ↥(U₁ ⊔ U₂)) =
      h.pairEquiv (μ₁ * w.1, μ₂ * w.2) := Subtype.ext (by
    show x (h.pairEquiv w : V) = (h.pairEquiv (μ₁ * w.1, μ₂ * w.2) : V)
    rw [coe_pairEquiv, act_pairMap hx₁ hx₂, coe_pairEquiv])
  rw [this, normPlaneIsometry_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

theorem psi_left {c : E} (hc : c ≠ 0) (hNc : D.Nm c = -1) {x : V ≃ₗ[K] V} {lam : E}
    (hx₁ : ∀ z, x (φ₁ z : V) = (φ₁ (lam * z) : V))
    (hx₂ : ∀ z, x (φ₂ z : V) = (φ₂ (lam * z) : V)) (r : ↥(U₁ ⊔ U₂)) :
    ∃ hr : x (r : V) ∈ U₁ ⊔ U₂, h.normPlaneIsometry hc hNc ⟨x r, hr⟩ =
      D.lmat lam * h.normPlaneIsometry hc hNc r := by
  obtain ⟨hr, h1⟩ := h.psi_act hc hNc hx₁ hx₂ r
  exact ⟨hr, by rw [h1, normPlaneIsometry_apply, D.lmat_mul_phi]⟩

theorem psi_right {c : E} (hc : c ≠ 0) (hNc : D.Nm c = -1) {x : V ≃ₗ[K] V} {eta : E}
    (hx₁ : ∀ z, x (φ₁ z : V) = (φ₁ (eta * z) : V))
    (hx₂ : ∀ z, x (φ₂ z : V) = (φ₂ (D.bar eta * z) : V)) (r : ↥(U₁ ⊔ U₂)) :
    ∃ hr : x (r : V) ∈ U₁ ⊔ U₂, h.normPlaneIsometry hc hNc ⟨x r, hr⟩ =
      h.normPlaneIsometry hc hNc r * D.lmat eta := by
  obtain ⟨hr, h1⟩ := h.psi_act hc hNc hx₁ hx₂ r
  exact ⟨hr, by rw [h1, normPlaneIsometry_apply, D.phi_mul_lmat]⟩

end NormPlanes

end Planes

end CFSG.RankThree.PartOne.KCOrthogonal
