module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.Filter.Orthogonal.OddReflections

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix QuadraticMap
open CFSG.ClassicalGroups.Orthogonal

theorem nine3_reflect_isConj {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) {P P' : HypPair Q}
    (hPP' : P.Orth P') {x y : V} (hx : Q x ≠ 0) (hy : Q y ≠ 0) (hxy : Q x = Q y) :
    ∃ g ∈ elementaryGroup Q, g * CFSG.ClassicalGroups.Orthogonal.reflect Q x * g⁻¹ =
      CFSG.ClassicalGroups.Orthogonal.reflect Q y := by
  have hx0 : x ≠ 0 := fun h => hx (by rw [h, map_zero])
  have hy0 : y ≠ 0 := fun h => hy (by rw [h, map_zero])
  obtain ⟨g, hg, hgx⟩ := exists_mem_elementaryGroup_apply_eq hQ hPP' hx0 hy0 hxy
  refine ⟨g, hg, ?_⟩
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_conj (elementaryGroup_le_orthogonalGroup Q hg) x,
    hgx]

theorem nine3_polar_eq_zero_or_smul_of_scalar_commute {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (h2nsq : ∀ t : K, t * t ≠ 2)
    {x y : V} (hx : Q x ≠ 0) (hy : Q y ≠ 0) (hxy : Q x = Q y) {lam : K} (hlam : lam ≠ 0)
    (h : ∀ v, CFSG.ClassicalGroups.Orthogonal.reflect Q x
        (CFSG.ClassicalGroups.Orthogonal.reflect Q y v) =
      lam • CFSG.ClassicalGroups.Orthogonal.reflect Q y
        (CFSG.ClassicalGroups.Orthogonal.reflect Q x v)) :
    polar Q x y = 0 ∨ ∃ c : K, c ≠ 0 ∧ y = c • x := by
  have hx0 : x ≠ 0 := fun h0 => hx (by rw [h0, map_zero])
  have hy0 : y ≠ 0 := fun h0 => hy (by rw [h0, map_zero])
  set c : K := polar Q x y / Q x with hcdef
  have hcx : CFSG.ClassicalGroups.Orthogonal.reflect Q x y = y - c • x := by
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hx, hcdef]
  have hcy : CFSG.ClassicalGroups.Orthogonal.reflect Q y x = x - c • y := by
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hy, hcdef]
    congr 1
    rw [polar_comm, hxy]
  have hax : CFSG.ClassicalGroups.Orthogonal.reflect Q x x = -x :=
    CFSG.GH74.Filter.reflect_apply_self hx
  have hby : CFSG.ClassicalGroups.Orthogonal.reflect Q y y = -y :=
    CFSG.GH74.Filter.reflect_apply_self hy
  have key : -x - c • y + c ^ 2 • x = lam • (-x + c • y) := by
    have h1 := h x
    rw [hcy, map_sub, map_smul, hax, hcx, map_neg, hcy] at h1
    have h2 : -x - c • (y - c • x) = -x - c • y + c ^ 2 • x := by module
    have h3 : lam • -(x - c • y) = lam • (-x + c • y) := by module
    rwa [h2, h3] at h1
  have hrel : (c ^ 2 - 1 + lam) • x = (c * (1 + lam)) • y := by
    have h' : -x - c • y + c ^ 2 • x = lam • (-x + c • y) := key
    linear_combination (norm := module) h'
  rcases eq_or_ne c 0 with hc | hc
  · left
    have hz : polar Q x y / Q x = 0 := by rw [← hcdef, hc]
    exact (div_eq_zero_iff.mp hz).resolve_right hx
  · rcases eq_or_ne (1 + lam) 0 with h1lam | h1lam
    · exfalso
      have hlam1 : lam = -1 := by linear_combination h1lam
      rw [hlam1] at hrel
      have hc2 : c ^ 2 = 2 := by
        have hz : (c ^ 2 - 1 + -1) • x = 0 := by rw [hrel]; simp
        have := (smul_eq_zero.mp hz).resolve_right hx0
        linear_combination this
      exact h2nsq c (by rwa [pow_two] at hc2)
    · right
      have hc1lam : c * (1 + lam) ≠ 0 := mul_ne_zero hc h1lam
      refine ⟨(c ^ 2 - 1 + lam) / (c * (1 + lam)), ?_, ?_⟩
      · intro hc'
        have hnum : c ^ 2 - 1 + lam = 0 := (div_eq_zero_iff.mp hc').resolve_right hc1lam
        rw [hnum, zero_smul] at hrel
        exact hy0 ((smul_eq_zero.mp hrel.symm).resolve_left hc1lam)
      · have h := congrArg (fun z => (c * (1 + lam))⁻¹ • z) hrel
        simp only [smul_smul, inv_mul_cancel₀ hc1lam, one_smul] at h
        rw [← h, div_eq_inv_mul, mul_comm]

theorem nine3_polar_eq_zero_of_mk_commute {K : Type} [Field K] (h2nsq : ∀ t : K, t * t ≠ 2)
    {Q : QuadraticForm K (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → K)} (hQ : (polarBilin Q).Nondegenerate)
    {x y : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → K} (hx : Q x ≠ 0) (hy : Q y ≠ 0) (hxy : Q x = Q y)
    (hnotprop : ∀ c : K, c ≠ 0 → y ≠ c • x)
    (h : Matrix.ProjGenLinGroup.mk
            ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K).symm
              (CFSG.ClassicalGroups.Orthogonal.reflect Q x)) *
         Matrix.ProjGenLinGroup.mk
            ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K).symm
              (CFSG.ClassicalGroups.Orthogonal.reflect Q y)) =
         Matrix.ProjGenLinGroup.mk
            ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K).symm
              (CFSG.ClassicalGroups.Orthogonal.reflect Q y)) *
         Matrix.ProjGenLinGroup.mk
            ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K).symm
              (CFSG.ClassicalGroups.Orthogonal.reflect Q x))) :
    polar Q x y = 0 := by
  set Ax : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K :=
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K).symm
      (CFSG.ClassicalGroups.Orthogonal.reflect Q x) with hAx
  set Ay : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K :=
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K).symm
      (CFSG.ClassicalGroups.Orthogonal.reflect Q y) with hAy
  have hmk : Matrix.ProjGenLinGroup.mk (Ax * Ay) = Matrix.ProjGenLinGroup.mk (Ay * Ax) := by
    rw [hAx, hAy, map_mul, map_mul]
    exact h
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hmk
  have hpoint : ∀ v, CFSG.ClassicalGroups.Orthogonal.reflect Q x
        (CFSG.ClassicalGroups.Orthogonal.reflect Q y v) =
      (u : K)⁻¹ • CFSG.ClassicalGroups.Orthogonal.reflect Q y
        (CFSG.ClassicalGroups.Orthogonal.reflect Q x v) := by
    intro v
    have hscalar_lin : ∀ w, CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K
        (Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2 ⊕ Fin 2) u) w = (u : K) • w := by
      intro w
      rw [toLinEquiv_apply, Matrix.GeneralLinearGroup.coe_scalar]
      ext i
      simp [Matrix.scalar, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    have h1 := congrArg (fun M : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K =>
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K M) hu
    rw [map_mul, map_mul, map_mul, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply] at h1
    have h2 := congrArg (fun g : (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → K) ≃ₗ[K]
      (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → K) => g v) h1
    simp only [LinearEquiv.mul_apply, hscalar_lin, map_smul] at h2
    calc CFSG.ClassicalGroups.Orthogonal.reflect Q x
          (CFSG.ClassicalGroups.Orthogonal.reflect Q y v)
        = (u : K)⁻¹ • ((u : K) • CFSG.ClassicalGroups.Orthogonal.reflect Q x
            (CFSG.ClassicalGroups.Orthogonal.reflect Q y v)) := by
          rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero u), one_smul]
      _ = (u : K)⁻¹ • CFSG.ClassicalGroups.Orthogonal.reflect Q y
            (CFSG.ClassicalGroups.Orthogonal.reflect Q x v) := by rw [h2]
  rcases nine3_polar_eq_zero_or_smul_of_scalar_commute h2nsq hx hy hxy
      (lam := (u : K)⁻¹) (inv_ne_zero (Units.ne_zero u)) hpoint with h0 | ⟨c, hc, hyc⟩
  · exact h0
  · exact absurd hyc (hnotprop c hc)


theorem nine3_reflect_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {x : V} {c : K} (hc : c ≠ 0) (hx : Q x ≠ 0) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q (c • x) =
      CFSG.ClassicalGroups.Orthogonal.reflect Q x := by
  have hcx : Q (c • x) ≠ 0 := by
    rw [QuadraticMap.map_smul, smul_eq_mul]
    exact mul_ne_zero (mul_ne_zero hc hc) hx
  refine LinearEquiv.ext fun y => ?_
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hcx,
    CFSG.ClassicalGroups.Orthogonal.reflect_apply hx, QuadraticMap.polar_smul_left,
    QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul, smul_smul]
  congr 1
  field_simp
  

theorem nine3_radical_quad_eq_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {p q : V} (hp : Q p ≠ 0) (hq : Q q = Q p)
    (hbeta : polar Q p q ≠ 0) (h3 : (3 : K) = 0) (hsq : ∀ t : K, t ≠ 0 → t * t = 1) :
    Q (polar Q p q • p - (2 * Q p) • q) = 0 := by
  have hQp1 : Q p * Q p = 1 := hsq _ hp
  have hbeta1 : polar Q p q * polar Q p q = 1 := hsq _ hbeta
  rw [sub_eq_add_neg, QuadraticMap.map_add (Q : V → K), QuadraticMap.map_neg, polar_neg_right,
    QuadraticMap.map_smul, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, smul_eq_mul, smul_eq_mul, hq]
  linear_combination (-(Q p)) * hbeta1 + (4 * Q p) * hQp1 + (Q p) * h3

end CFSG.LocalAnalysis.WeakClosure81
