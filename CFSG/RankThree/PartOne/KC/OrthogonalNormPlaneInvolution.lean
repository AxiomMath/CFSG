module

public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneFactors

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

section ReflectPair

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {u v : V}

theorem reflectPair_apply (hu : Q u = 1) (hv : Q v = 1) (huv : polar Q u v = 0) (x : V) :
    (reflect Q u * reflect Q v) x = x - polar Q u x • u - polar Q v x • v := by
  have hu0 : Q u ≠ 0 := by rw [hu]; exact one_ne_zero
  have hv0 : Q v ≠ 0 := by rw [hv]; exact one_ne_zero
  rw [LinearEquiv.mul_apply, reflect_apply hv0 x, map_sub, map_smul,
    reflect_apply_of_polar_eq_zero huv, reflect_apply hu0 x, hu, hv, div_one, div_one]

theorem reflectPair_comm (hu : Q u = 1) (hv : Q v = 1) (huv : polar Q u v = 0) :
    reflect Q u * reflect Q v = reflect Q v * reflect Q u := by
  have hvu : polar Q v u = 0 := by rw [polar_comm]; exact huv
  refine LinearEquiv.ext fun x => ?_
  rw [reflectPair_apply hu hv huv, reflectPair_apply hv hu hvu]
  abel

theorem reflectPair_sq (hu : Q u = 1) (hv : Q v = 1) (huv : polar Q u v = 0) :
    (reflect Q u * reflect Q v) ^ 2 = 1 := by
  have hc : Commute (reflect Q u) (reflect Q v) := reflectPair_comm hu hv huv
  rw [hc.mul_pow, pow_two, pow_two, reflect_mul_self, reflect_mul_self, one_mul]

theorem reflectPair_mem :
    reflect Q u * reflect Q v ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  mul_mem (reflect_mem_orthogonalGroup Q u) (reflect_mem_orthogonalGroup Q v)

theorem reflectPair_fix (hu : Q u = 1) (hv : Q v = 1) (huv : polar Q u v = 0) {x : V}
    (hxu : polar Q u x = 0) (hxv : polar Q v x = 0) : (reflect Q u * reflect Q v) x = x := by
  rw [reflectPair_apply hu hv huv, hxu, hxv, zero_smul, zero_smul, sub_zero, sub_zero]

theorem reflectPair_ne_one (hu : Q u = 1) (hv : Q v = 1) (huv : polar Q u v = 0)
    (hli : ∀ a b : K, a • u + b • v = 0 → a = 0 ∧ b = 0) (hx : ∃ x, polar Q u x ≠ 0) :
    reflect Q u * reflect Q v ≠ 1 := by
  obtain ⟨x, hx⟩ := hx
  intro h
  have h1 := reflectPair_apply hu hv huv x
  rw [h] at h1
  change x = x - polar Q u x • u - polar Q v x • v at h1
  have h2 : polar Q u x • u + polar Q v x • v = 0 := by
    have h3 : x - polar Q u x • u - polar Q v x • v = x := h1.symm
    rw [sub_sub] at h3
    exact sub_eq_self.mp h3
  exact hx (hli _ _ h2).1

theorem reflectPair_eq_eichler (h2 : (2 : K) = 0) (hu : Q u = 1) (hv : Q v = 1)
    (huv : polar Q u v = 0) : reflect Q u * reflect Q v = eichler Q (u + v) u := by
  have hvu : polar Q v u = 0 := by rw [polar_comm]; exact huv
  have hQ : Q (u + v) = 0 := by
    rw [QuadraticMap.map_add Q u v, hu, hv, huv]
    linear_combination h2
  have hp : polar Q (u + v) u = 0 := by
    rw [polar_add_left, polar_self_eq_two_mul, hu, hvu]
    linear_combination h2
  refine LinearEquiv.ext fun x => ?_
  rw [reflectPair_apply hu hv huv, eichler_apply hQ hp, polar_add_right, hu, polar_comm Q u x,
    polar_comm Q v x]
  have h3 : (2 : K) • v = 0 := by rw [h2, zero_smul]
  linear_combination (norm := module) (polar Q x u) • h3

end ReflectPair

section Planes

variable {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E] {D : QuadData K E}
  {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {U₁ U₂ : Submodule K V} {φ₁ : E →ₗ[K] U₁} {φ₂ : E →ₗ[K] U₂}

namespace NormPlanes

variable (h : NormPlanes D Q U₁ U₂ φ₁ φ₂)

include h

theorem Q_one₁ : Q (φ₁ 1 : V) = 1 := by rw [h.norm₁, D.Nm_one]

theorem Q_one₂ : Q (φ₂ 1 : V) = 1 := by rw [h.norm₂, D.Nm_one]

theorem polar_one : polar Q (φ₁ 1 : V) (φ₂ 1 : V) = 0 := h.orth _ (φ₁ 1).2 _ (φ₂ 1).2

theorem polar_phi₁ (z : E) : polar Q (φ₁ 1 : V) (φ₁ z : V) = D.tr z := by
  have hadd : (φ₁ 1 : V) + (φ₁ z : V) = (φ₁ (z + 1) : V) := by
    rw [← Submodule.coe_add, ← map_add, add_comm]
  rw [polar, hadd]
  simp only [h.norm₁, D.tr_add_Nm, D.Nm_one]
  ring

theorem polar_phi₂ (z : E) : polar Q (φ₂ 1 : V) (φ₂ z : V) = D.tr z := by
  have hadd : (φ₂ 1 : V) + (φ₂ z : V) = (φ₂ (z + 1) : V) := by
    rw [← Submodule.coe_add, ← map_add, add_comm]
  rw [polar, hadd]
  simp only [h.norm₂, D.tr_add_Nm, D.Nm_one]
  ring

theorem polar_phi₁₂ (z : E) : polar Q (φ₁ 1 : V) (φ₂ z : V) = 0 := h.orth _ (φ₁ 1).2 _ (φ₂ z).2

theorem polar_phi₂₁ (z : E) : polar Q (φ₂ 1 : V) (φ₁ z : V) = 0 := by
  rw [polar_comm]
  exact h.orth _ (φ₁ z).2 _ (φ₂ 1).2

theorem reflectPair_pairMap (z₁ z₂ : E) :
    (reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V)) (pairMap φ₁ φ₂ (z₁, z₂)) =
      pairMap φ₁ φ₂ (-(D.bar z₁), -(D.bar z₂)) := by
  have hu : polar Q (φ₁ 1 : V) (pairMap φ₁ φ₂ (z₁, z₂)) = D.tr z₁ := by
    rw [pairMap_apply, polar_add_right, h.polar_phi₁, h.polar_phi₁₂, add_zero]
  have hv : polar Q (φ₂ 1 : V) (pairMap φ₁ φ₂ (z₁, z₂)) = D.tr z₂ := by
    rw [pairMap_apply, polar_add_right, h.polar_phi₂₁, h.polar_phi₂, zero_add]
  have e1 : φ₁ (-(D.bar z₁)) = φ₁ z₁ - D.tr z₁ • φ₁ 1 := by
    rw [← map_smul, ← map_sub]
    congr 1
    rw [Algebra.smul_def, mul_one, D.algebraMap_tr]
    ring
  have e2 : φ₂ (-(D.bar z₂)) = φ₂ z₂ - D.tr z₂ • φ₂ 1 := by
    rw [← map_smul, ← map_sub]
    congr 1
    rw [Algebra.smul_def, mul_one, D.algebraMap_tr]
    ring
  rw [reflectPair_apply h.Q_one₁ h.Q_one₂ h.polar_one, hu, hv]
  simp only [pairMap_apply, e1, e2, Submodule.coe_sub, Submodule.coe_smul]
  abel

theorem psi_pairEquiv {c : E} (hc : c ≠ 0) (hNc : D.Nm c = -1) (w : E × E) :
    h.normPlaneIsometry hc hNc (h.pairEquiv w) = D.phi c w := by
  rw [normPlaneIsometry_apply, LinearEquiv.symm_apply_apply]

theorem symm_phi {c : E} (hc : c ≠ 0) (hNc : D.Nm c = -1) (w : E × E) :
    (h.normPlaneIsometry hc hNc).symm (D.phi c w) = h.pairEquiv w := by
  rw [← h.psi_pairEquiv hc hNc w, QuadraticMap.IsometryEquiv.symm_apply_apply]

end NormPlanes

end Planes

section Mem

variable {K : Type*} [Field K] [Finite K] {E : Type*} [Field E] [Algebra K E] {D : QuadData K E}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
  {U₁ U₂ : Submodule K V} {φ₁ : E →ₗ[K] U₁} {φ₂ : E →ₗ[K] U₂}

namespace NormPlanes

variable (h : NormPlanes D Q U₁ U₂ φ₁ φ₂) {c : E} (hc : c ≠ 0) (hNc : D.Nm c = -1)

include h hc hNc

theorem reflectPair_mem_supported (hK2 : Nat.card K ≠ 2) (hK3 : Nat.card K ≠ 3) :
    reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V) ∈ supportedOrthDerived Q (U₁ ⊔ U₂) := by
  rw [h.supported_eq_map hc hNc hK2 hK3]
  have hAA : (D.lmat c * D.cmat) * (D.cmat * D.lmat c⁻¹) = 1 := D.lmatC_mul_inv hc
  have hdetA : (D.lmat c * D.cmat).det = 1 := D.lmatC_det hNc
  have hdetAi : (D.cmat * D.lmat c⁻¹).det = 1 := by
    have := congrArg Matrix.det hAA
    rw [Matrix.det_mul, hdetA, one_mul, Matrix.det_one] at this
    exact this
  let A : Matrix.SpecialLinearGroup (Fin 2) K := ⟨D.lmat c * D.cmat, hdetA⟩
  let B : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨-(D.lmat c * D.cmat), by rw [Matrix.det_neg, hdetA]; simp⟩
  let Bi : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨-(D.cmat * D.lmat c⁻¹), by rw [Matrix.det_neg, hdetAi]; simp⟩
  have hBi : B⁻¹ = Bi := inv_eq_of_mul_eq_one_right (Subtype.ext (by
    show (-(D.lmat c * D.cmat)) * (-(D.cmat * D.lmat c⁻¹)) = 1
    rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, hAA]))
  refine ⟨specialRho (A, B), ⟨(A, B), rfl⟩, ?_⟩
  have hfix_w : ∀ w ∈ orthPerp Q (U₁ ⊔ U₂),
      (reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V)) w = w := by
    intro w hw
    refine reflectPair_fix h.Q_one₁ h.Q_one₂ h.polar_one ?_ ?_
    · exact mem_orthPerp.mp hw _ (Submodule.mem_sup_left (φ₁ 1).2)
    · exact mem_orthPerp.mp hw _ (Submodule.mem_sup_right (φ₂ 1).2)
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨r, w, rfl⟩ := exists_add_of_isCompl (h.isCompl hc hNc) v
  rw [map_add, map_add, h.factorHom_fix hc hNc _ w.2, hfix_w w w.2]
  congr 1
  obtain ⟨w₀, rfl⟩ := h.pairEquiv.surjective r
  obtain ⟨z₁, z₂⟩ := w₀
  rw [h.factorHom_apply_mem hc hNc, h.coe_pairEquiv, h.reflectPair_pairMap,
    h.psi_pairEquiv hc hNc, specialRho_apply, hBi]
  have key : (D.lmat c * D.cmat) * D.phi c (z₁, z₂) * (-(D.cmat * D.lmat c⁻¹)) =
      D.phi c (-(D.bar z₁), -(D.bar z₂)) := by
    rw [Matrix.mul_neg, D.lmat_cmat_phi hc (z₁, z₂), ← Prod.neg_mk, D.phi_neg]
  show ((h.normPlaneIsometry hc hNc).symm
    ((D.lmat c * D.cmat) * D.phi c (z₁, z₂) * (-(D.cmat * D.lmat c⁻¹))) : V) = _
  rw [key, h.symm_phi hc hNc]
  rfl

end NormPlanes

end Mem

end CFSG.RankThree.PartOne.KCOrthogonal
