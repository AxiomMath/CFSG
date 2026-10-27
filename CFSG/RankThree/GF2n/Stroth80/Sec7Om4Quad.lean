module

public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped Matrix

theorem sec7_minusTwo_singular_perp {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {u d : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K} (hu0 : u ≠ 0) (hu : quadMinus 2 K b c u = 0)
    (hd : quadMinus 2 K b c d = 0) (hud : polar (quadMinus 2 K b c) u d = 0) :
    ∃ a : K, d = a • u := by
  by_contra hne
  push Not at hne
  have hadd : ∀ v w : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K,
      quadMinus 2 K b c (v + w) = quadMinus 2 K b c v + quadMinus 2 K b c w +
        polar (quadMinus 2 K b c) v w := fun v w => by
    simp only [polar]
    abel
  have hli : LinearIndependent K ![u, d] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right hu0, rfl⟩
    · exfalso
      refine hne (-(s * t⁻¹)) ?_
      have h1 : t⁻¹ • (s • u + t • d) = 0 := by rw [hst, smul_zero]
      rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ht, one_smul] at h1
      rw [neg_smul, mul_comm s t⁻¹]
      exact eq_neg_of_add_eq_zero_right h1
  have hfin : Module.finrank K (Submodule.span K (Set.range ![u, d])) = 2 := by
    rw [finrank_span_eq_card hli]
    simp
  obtain ⟨v, hvU, hv⟩ := exists_quadMinus_ne_zero_of_finrank (by norm_num) hirr _ hfin
  rw [Submodule.mem_span_range_iff_exists_fun] at hvU
  obtain ⟨α, rfl⟩ := hvU
  apply hv
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [hadd, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left, polar_smul_right,
    hu, hd, hud]
  simp

theorem sec7_mulVec_eq_self_of_root {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Q : QuadraticForm K (ι → K)} {u u' : ι → K} {M : Matrix ι ι K}
    (hw : ∀ d : ι → K, Q d = 0 → polar Q u d = 0 → ∃ a : K, d = a • u)
    (hu : Q u = 0) (hiso : ∀ v, Q (M *ᵥ v) = Q v)
    (hperp : ∀ x, polar Q u' x = 0 → ∃ c : K, M *ᵥ x - x = c • u')
    (hmov : ∀ x, polar Q u' (M *ᵥ x - x) = 0) (huu' : polar Q u u' ≠ 0)
    (h0 : polar Q u (M *ᵥ u) = 0) (x : ι → K) : M *ᵥ x = x := by
  have hpol : ∀ v w : ι → K, polar Q (M *ᵥ v) (M *ᵥ w) = polar Q v w := by
    intro v w
    simp only [polar, ← Matrix.mulVec_add, hiso]
  have hadd : ∀ v w : ι → K, Q (v + w) = Q v + Q w + polar Q v w := fun v w => by
    simp only [polar]
    abel
  have hu'u : polar Q u' u ≠ 0 := by
    rwa [polar_comm]
  have hpud : polar Q u (M *ᵥ u - u) = 0 := by
    rw [polar_sub_right, h0, polar_self, hu, smul_zero, sub_zero]
  have hgu : M *ᵥ u = u := by
    have hQd : Q (M *ᵥ u - u) = 0 := by
      have h1 : Q (M *ᵥ u - u + u) = 0 := by
        rw [sub_add_cancel, hiso u, hu]
      rw [hadd, hu, add_zero, polar_comm, hpud, add_zero] at h1
      exact h1
    obtain ⟨a, ha⟩ := hw _ hQd hpud
    have hpa : a • polar Q u' u = 0 := by
      rw [← polar_smul_right, ← ha]
      exact hmov u
    have ha0 : a = 0 := (smul_eq_zero.mp hpa).resolve_right hu'u
    rw [ha0, zero_smul, sub_eq_zero] at ha
    exact ha
  have hfix : ∀ y : ι → K, polar Q u' y = 0 → M *ᵥ y = y := by
    intro y hy
    obtain ⟨c, hc⟩ := hperp y hy
    have h2 : polar Q u (M *ᵥ y) = polar Q u y := by
      have h3 := hpol u y
      rwa [hgu] at h3
    have h4 : c • polar Q u u' = 0 := by
      rw [← polar_smul_right, ← hc, polar_sub_right, h2, sub_self]
    have hc0 : c = 0 := (smul_eq_zero.mp h4).resolve_right huu'
    rw [hc0, zero_smul, sub_eq_zero] at hc
    exact hc
  obtain ⟨s, hs⟩ : ∃ s : K, polar Q u' x = s * polar Q u' u :=
    ⟨polar Q u' x * (polar Q u' u)⁻¹, by rw [mul_assoc, inv_mul_cancel₀ hu'u, mul_one]⟩
  have hy : polar Q u' (x - s • u) = 0 := by
    rw [polar_sub_right, polar_smul_right, smul_eq_mul, hs, sub_self]
  have hyfix := hfix _ hy
  calc M *ᵥ x = M *ᵥ (x - s • u + s • u) := by rw [sub_add_cancel]
    _ = M *ᵥ (x - s • u) + s • M *ᵥ u := by rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    _ = x := by rw [hyfix, hgu, sub_add_cancel]

theorem sec7_polar_apply_ne_zero_of_mem_rootGroupGL {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {u u' : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K} (hu : quadMinus 2 K b c u = 0)
    (hu' : quadMinus 2 K b c u' = 0) (hu0 : u ≠ 0) (hu'0 : u' ≠ 0)
    (huu' : polar (quadMinus 2 K b c) u u' ≠ 0)
    {A : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K}
    (hA : A ∈ rootGroupGL (quadMinus 2 K b c) u') (hA1 : A ≠ 1) :
    polar (quadMinus 2 K b c) u
      ((A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ u)
      ≠ 0 := by
  intro h0
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  obtain ⟨hiso, -, hperp, hmov⟩ := (mem_rootGroupGL_iff hQ hu' hu'0).mp hA
  have hw : ∀ d : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K, quadMinus 2 K b c d = 0 →
      polar (quadMinus 2 K b c) u d = 0 → ∃ a : K, d = a • u :=
    fun d hd hud => sec7_minusTwo_singular_perp hirr hu0 hu hd hud
  have hall := sec7_mulVec_eq_self_of_root hw hu hiso hperp hmov huu' h0
  apply hA1
  apply Units.ext
  rw [Units.val_one]
  exact Matrix.ext_iff_mulVec.mpr fun v => by rw [Matrix.one_mulVec]; exact hall v

end CFSG.RankThree.GF2n.Stroth80
