module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailShortRootExchange
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

@[expose] noncomputable def w183ElemAct {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) :
    ↥(elementaryGroup Q) →* AddMonoid.End V where
  toFun g := ((g : V ≃ₗ[K] V) : V →ₗ[K] V).toAddMonoidHom
  map_one' := by
    ext v
    rfl
  map_mul' g h := by
    ext v
    rfl

theorem w183ElemAct_apply {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (g : ↥(elementaryGroup Q)) (z : V) :
    w183ElemAct Q g z = (g : V ≃ₗ[K] V) z :=
  rfl

@[expose] noncomputable def w183El {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (c w : V) : ↥(elementaryGroup Q) :=
  ⟨eichler Q c w, eichler_mem_elementaryGroup Q c w⟩

theorem w183El_coe {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (c w : V) :
    ((w183El Q c w : ↥(elementaryGroup Q)) : V ≃ₗ[K] V) = eichler Q c w :=
  rfl

theorem w183El_mul {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {c u v : V} (hu : polar Q c u = 0) (hv : polar Q c v = 0) :
    w183El Q c u * w183El Q c v = w183El Q c (u + v) :=
  Subtype.ext (eichler_mul hu hv)

theorem w183_self_add_eq_zero {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
    (m : V) : m + m = 0 := by
  rw [← two_smul K m, CharTwo.two_eq_zero, zero_smul]

@[expose] def W183Torus {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) (c : K) (d : V ≃ₗ[K] V) : Prop :=
  d P.e = c • P.e ∧ d P.f = c⁻¹ • P.f ∧ ∀ z ∈ P.perp, d z = z

theorem w183_torus_exists {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (P : HypPair Q) {v : V} (hv : v ∈ P.perp)
    (hQv : Q v ≠ 0) {c : K} (hc : c ≠ 0) :
    ∃ d ∈ elementaryGroup Q, W183Torus P c d := by
  obtain ⟨α, hα⟩ := FiniteField.isSquare_of_char_two (F := K) (ringChar.eq K 2) c⁻¹
  have hα0 : α ≠ 0 := fun h => by
    rw [h, mul_zero] at hα
    exact inv_ne_zero hc hα
  have hQav : Q (α • v) = c⁻¹ * Q v := by rw [map_smul_eq_sq, pow_two, ← hα]
  have hav : α • v ∈ P.perp := P.perp.smul_mem α hv
  have hdav : Q (α • v) ≠ 0 := by rw [hQav]; exact mul_ne_zero (inv_ne_zero hc) hQv
  have hav' : -(α • v) ∈ P.perp := P.perp.neg_mem hav
  have hdav' : Q (-(α • v)) ≠ 0 := by rw [QuadraticMap.map_neg]; exact hdav
  refine ⟨shortWeyl P v * (shortWeyl P (α • v))⁻¹, mul_mem (shortWeyl_mem P v)
    (inv_mem (shortWeyl_mem P _)), ?_, ?_, ?_⟩
  · have := shortWeyl_mul_inv_e P hv hQv hav' hdav'
    rw [neg_neg, QuadraticMap.map_neg, hQav] at this
    rw [this]
    congr 1
    field_simp
  · have := shortWeyl_mul_inv_f P hv hQv hav' hdav'
    rw [neg_neg, QuadraticMap.map_neg, hQav] at this
    rw [this]
    congr 1
    field_simp
  · intro z hz
    rw [LinearEquiv.mul_apply, shortWeyl_inv P hav hdav, shortWeyl_perp P hav hdav hz]
    have hw : z - (polar Q z (α • v) * (Q (α • v))⁻¹) • α • v =
        z - (polar Q z v * (Q v)⁻¹) • v := by
      rw [polar_smul_right_eq, hQav, smul_smul, hα]
      congr 2
      field_simp
    rw [hw]
    have hwP : z - (polar Q z v * (Q v)⁻¹) • v ∈ P.perp :=
      P.perp.sub_mem hz (P.perp.smul_mem _ hv)
    rw [shortWeyl_perp P hv hQv hwP, polar_sub_left, polar_smul_left_eq, polar_self_eq_two_mul,
      CharTwo.two_eq_zero]
    simp only [zero_mul, mul_zero, sub_zero, sub_sub, ← add_smul]
    rw [CharTwo.add_self_eq_zero, zero_smul, sub_zero]

theorem w183_torus_hom {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q)
    (hex : ∀ c : K, c ≠ 0 → ∃ d ∈ elementaryGroup Q, W183Torus P c d) :
    ∃ φ : Kˣ →* ↥(elementaryGroup Q), ∀ c : Kˣ, W183Torus P (c : K) (φ c : V ≃ₗ[K] V) := by
  have huniq : ∀ (c : K) (d d' : V ≃ₗ[K] V), W183Torus P c d → W183Torus P c d' → d = d' := by
    rintro c d d' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine LinearEquiv.ext fun z => ?_
    conv_lhs => rw [P.eq_add_proj z]
    conv_rhs => rw [P.eq_add_proj z]
    simp only [map_add, map_smul, h1, h1', h2, h2', h3 _ (P.proj_mem_perp z),
      h3' _ (P.proj_mem_perp z)]
  have hmul : ∀ (c c' : K) (d d' : V ≃ₗ[K] V), W183Torus P c d → W183Torus P c' d' →
      W183Torus P (c * c') (d * d') := by
    rintro c c' d d' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨?_, ?_, fun z hz => ?_⟩
    · rw [LinearEquiv.mul_apply, h1', map_smul, h1, smul_smul, mul_comm]
    · rw [LinearEquiv.mul_apply, h2', map_smul, h2, smul_smul, mul_inv, mul_comm]
    · rw [LinearEquiv.mul_apply, h3' z hz, h3 z hz]
  have hone : W183Torus P 1 (1 : V ≃ₗ[K] V) :=
    ⟨by simp, by simp, fun z _ => rfl⟩
  choose! D hDE hDT using hex
  refine ⟨{ toFun := fun c => ⟨D c, hDE c c.ne_zero⟩
            map_one' := Subtype.ext (huniq 1 _ _ (by simpa using hDT 1 one_ne_zero) hone)
            map_mul' := fun c c' => Subtype.ext (huniq (c * c' : Kˣ) _ _
              (by simpa using hDT (c * c' : Kˣ) (c * c').ne_zero) (hmul _ _ _ _
                (hDT c c.ne_zero) (hDT c' c'.ne_zero))) },
    fun c => hDT c c.ne_zero⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
