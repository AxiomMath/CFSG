module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmIso
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open Matrix QuadraticMap

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem exists_heis_inv_skewNonsquare [Finite K] (hK2 : ringChar K ≠ 2) (hd : 5 ≤ d)
    {A : GL (Fin d) K} {μ : K} (hμ0 : μ ≠ 0) (hAQ : ∀ v, Q (A.val *ᵥ v) = μ * Q v)
    (hAA : A.val * A.val = (-μ) • 1) (hns : ∀ l : K, l ^ 2 ≠ -μ) :
    ∃ u z : Fin d → K, u ≠ 0 ∧ Q u = 0 ∧ A.val *ᵥ u ∉ Submodule.span K {u} ∧
      polar Q u (A.val *ᵥ u) = 0 ∧ polar Q u (A.val *ᵥ z) = 0 ∧
      polar Q (A.val *ᵥ u) (A.val *ᵥ z) = 0 ∧ polar Q u z = 0 ∧ polar Q (A.val *ᵥ u) z = 0 ∧
      polar Q (A.val *ᵥ z) z = 0 ∧ A.val *ᵥ z ∉ Submodule.span K {u, A.val *ᵥ u} := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hTT : ∀ v : Fin d → K, A.val *ᵥ (A.val *ᵥ v) = (-μ) • v := by
    intro v
    rw [Matrix.mulVec_mulVec, hAA, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hBAA : ∀ x y : Fin d → K,
      polar Q (A.val *ᵥ x) (A.val *ᵥ y) = μ * polar Q x y := by
    intro x y
    simp only [QuadraticMap.polar]
    rw [← Matrix.mulVec_add, hAQ, hAQ, hAQ]
    ring
  have hskew : ∀ x y : Fin d → K,
      polar Q (A.val *ᵥ x) y = -polar Q x (A.val *ᵥ y) := by
    intro x y
    have h1 := hBAA x (A.val *ᵥ y)
    rw [hTT y, QuadraticMap.polar_smul_right, smul_eq_mul] at h1
    have h2' : μ * polar Q (A.val *ᵥ x) y = μ * (-polar Q x (A.val *ᵥ y)) := by
      linear_combination -h1
    exact mul_left_cancel₀ hμ0 h2'
  have hself : ∀ x : Fin d → K, polar Q x (A.val *ᵥ x) = 0 := by
    intro x
    have h1 := hskew x x
    rw [QuadraticMap.polar_comm (⇑Q) (A.val *ᵥ x) x] at h1
    have h3 : (2 : K) * polar Q x (A.val *ᵥ x) = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h3).resolve_left h2
  have heigen : ∀ (v : Fin d → K) (t : K), v ≠ 0 → A.val *ᵥ v = t • v → False := by
    intro v t hv hvt
    have h1 : A.val *ᵥ (A.val *ᵥ v) = t ^ 2 • v := by
      rw [hvt, Matrix.mulVec_smul, hvt, smul_smul, pow_two]
    rw [hTT v] at h1
    have h3 : (t ^ 2 - -μ) • v = 0 := by
      rw [sub_smul, h1, sub_self]
    have h4 : t ^ 2 - -μ = 0 := (smul_eq_zero.mp h3).resolve_right hv
    exact hns t (sub_eq_zero.mp h4)
  obtain ⟨u, -, hu0, hu⟩ :=
    exists_singular_of_three_le_finrank hK2 Q (W := ⊤) (by
      rw [finrank_top, Module.finrank_fin_fun]
      omega)
  have hAu : A.val *ᵥ u ∉ Submodule.span K ({u} : Set (Fin d → K)) := by
    intro h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
    exact heigen u a hu0 ha.symm
  let f : (Fin d → K) →ₗ[K] (K × K) :=
    (polarBilin Q u).prod (polarBilin Q (A.val *ᵥ u))
  have hfv : ∀ x, f x = (polar Q u x, polar Q (A.val *ᵥ u) x) := by
    intro x
    simp only [f, LinearMap.prod_apply, Function.prod_apply, polarBilin_apply_apply]
  have hrange_le : Module.finrank K (LinearMap.range f) ≤ 2 := by
    have h := Submodule.finrank_mono (le_top : LinearMap.range f ≤ ⊤)
    rw [finrank_top, Module.finrank_prod, Module.finrank_self] at h
    omega
  have hker_ge : 3 ≤ Module.finrank K (LinearMap.ker f) := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    rw [Module.finrank_fin_fun] at h
    omega
  have hspan_le : Module.finrank K
      (Submodule.span K ({u, A.val *ᵥ u} : Set (Fin d → K))) ≤ 2 := by
    have h := finrank_span_le_card (R := K) ({u, A.val *ᵥ u} : Set (Fin d → K))
    refine h.trans ?_
    simpa using (Finset.card_le_two (a := u) (b := A.val *ᵥ u))
  have hnotle : ¬ LinearMap.ker f ≤
      Submodule.span K ({u, A.val *ᵥ u} : Set (Fin d → K)) := by
    intro hle
    have h := Submodule.finrank_mono hle
    omega
  obtain ⟨z, hzk, hzs⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hzm : polar Q u z = 0 ∧ polar Q (A.val *ᵥ u) z = 0 := by
    have h0 : f z = 0 := LinearMap.mem_ker.mp hzk
    rw [hfv z] at h0
    exact Prod.mk_eq_zero.mp h0
  obtain ⟨hzu, hzAu⟩ := hzm
  have hstab : ∀ w ∈ Submodule.span K ({u, A.val *ᵥ u} : Set (Fin d → K)),
      A.val *ᵥ w ∈ Submodule.span K ({u, A.val *ᵥ u} : Set (Fin d → K)) := by
    intro w hw
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · rintro x (rfl | rfl)
      · exact Submodule.subset_span (by simp)
      · rw [hTT u]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [Matrix.mulVec_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      rw [Matrix.mulVec_add]
      exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [Matrix.mulVec_smul]
      exact Submodule.smul_mem _ _ hx
  have hAz : A.val *ᵥ z ∉ Submodule.span K ({u, A.val *ᵥ u} : Set (Fin d → K)) := by
    intro h
    apply hzs
    have h1 : A.val *ᵥ (A.val *ᵥ z) ∈
        Submodule.span K ({u, A.val *ᵥ u} : Set (Fin d → K)) := hstab _ h
    rw [hTT z] at h1
    rw [show z = (-μ)⁻¹ • ((-μ) • z) by
      rw [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hμ0), one_smul]]
    exact Submodule.smul_mem _ _ h1
  have h5 : polar Q u (A.val *ᵥ z) = 0 := by
    have h := hskew u z
    rw [hzAu] at h
    exact neg_eq_zero.mp h.symm
  have h6 : polar Q (A.val *ᵥ u) (A.val *ᵥ z) = 0 := by
    rw [hBAA u z, hzu, mul_zero]
  refine ⟨u, z, hu0, hu, hAu, hself u, h5, h6, hzu, hzAu, ?_, hAz⟩
  exact (QuadraticMap.polar_comm (⇑Q) (A.val *ᵥ z) z).trans (hself z)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
