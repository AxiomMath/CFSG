module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmIso

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

private noncomputable def selfAdjointForm (Q : QuadraticForm K (Fin d → K))
    (A : Matrix (Fin d) (Fin d) K) : QuadraticForm K (Fin d → K) :=
  LinearMap.BilinMap.toQuadraticMap ((polarBilin Q).compl₂ (Matrix.toLin' A))

private theorem selfAdjointForm_apply (Q : QuadraticForm K (Fin d → K))
    (A : Matrix (Fin d) (Fin d) K) (x : Fin d → K) :
    selfAdjointForm Q A x = polar Q x (A *ᵥ x) := by
  rw [selfAdjointForm, LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.compl₂_apply,
    Matrix.toLin'_apply, polarBilin_apply_apply]

theorem exists_eichler_inv_selfAdjoint [Finite K] (hK2 : ringChar K ≠ 2) (hd : 5 ≤ d)
    {A : GL (Fin d) K} {μ : K} (hμ0 : μ ≠ 0) (hAQ : ∀ v, Q (A.val *ᵥ v) = μ * Q v)
    (hAA : A.val * A.val = μ • 1) (hns : ∀ a : K, A.val ≠ a • 1) :
    ∃ u w : Fin d → K, u ≠ 0 ∧ Q u = 0 ∧ polar Q u w = 0 ∧ w ∉ Submodule.span K {u} ∧
      eichler Q (A.val *ᵥ u) (μ⁻¹ • (A.val *ᵥ w)) = eichler Q u (-w) := by
  classical
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hB : ∀ x y : Fin d → K,
      polar Q (A.val *ᵥ x) (A.val *ᵥ y) = μ * polar Q x y := by
    intro x y
    have hx := hAQ x
    have hy := hAQ y
    have hxy := hAQ (x + y)
    rw [mulVec_add] at hxy
    unfold QuadraticMap.polar
    rw [hxy, hx, hy, QuadraticMap.map_add Q]
    ring
  have hAAv : ∀ v : Fin d → K, A.val *ᵥ (A.val *ᵥ v) = μ • v := by
    intro v
    rw [mulVec_mulVec, hAA, smul_mulVec, one_mulVec]
  obtain ⟨u, hu0, hu, huAu⟩ := exists_common_singular hK2 hd Q (selfAdjointForm Q A.val)
  rw [selfAdjointForm_apply] at huAu
  by_cases hmem : A.val *ᵥ u ∈ Submodule.span K {u}
  ·
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have hAu_eq : A.val *ᵥ u = a • u := ha.symm
    have ha2 : a ^ 2 = μ := by
      have h1 : A.val *ᵥ (A.val *ᵥ u) = a ^ 2 • u := by
        rw [hAu_eq, mulVec_smul, hAu_eq, smul_smul, _root_.sq]
      rw [hAAv u] at h1
      exact (smul_left_injective K hu0 h1).symm
    have haa : a * a = μ := by rw [← _root_.sq, ha2]
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num : 2 ≠ 0)] at ha2
      exact hμ0 ha2.symm
    have hy : ∃ y : Fin d → K, A.val *ᵥ y ≠ a • y := by
      by_contra h
      push Not at h
      exact hns a (by
        rw [Matrix.ext_iff_mulVec]
        intro v
        rw [h v, smul_mulVec, one_mulVec])
    obtain ⟨y, hy⟩ := hy
    set w : Fin d → K := A.val *ᵥ y - a • y with hw_def
    have hw0 : w ≠ 0 := fun h => hy (sub_eq_zero.mp (hw_def.symm.trans h))
    have hAw : A.val *ᵥ w = (-a) • w := by
      have h1 : A.val *ᵥ w = μ • y - a • (A.val *ᵥ y) := by
        rw [hw_def, mulVec_sub, mulVec_smul, hAAv y]
      rw [h1, hw_def, neg_smul, smul_sub, smul_smul, haa]
      module
    have hwmem : w ∉ Submodule.span K {u} := by
      intro hwspan
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hwspan
      have hcw : A.val *ᵥ w = a • w := by
        rw [← hc, mulVec_smul, hAu_eq, smul_smul, smul_smul, mul_comm c a]
      have haweq : a • w = (-a) • w := by rw [← hAw, hcw]
      have hcontr : a = -a := smul_left_injective K hw0 haweq
      have h2a : (2 : K) * a ≠ 0 := mul_ne_zero h2 ha0
      exact h2a (by linear_combination hcontr)
    have hBuw : polar Q u w = 0 := by
      have h1 := hB u w
      rw [hAu_eq, hAw, polar_smul_left_eq, polar_smul_right_eq] at h1
      have h1' : -μ * polar Q u w = μ * polar Q u w := by
        rw [← h1, ← haa]
        ring
      have h2' : (2 : K) * (μ * polar Q u w) = 0 := by
        linear_combination -h1'
      have hμB : μ * polar Q u w = 0 := (mul_eq_zero.mp h2').resolve_left h2
      exact (mul_eq_zero.mp hμB).resolve_left hμ0
    refine ⟨u, w, hu0, hu, hBuw, hwmem, ?_⟩
    rw [hAu_eq, hAw, eichler_smul_left]
    have harg : a • (μ⁻¹ • ((-a) • w)) = -w := by
      rw [smul_smul, smul_smul]
      rw [show a * μ⁻¹ * -a = -1 by
        rw [show a * μ⁻¹ * -a = -((a * a) * μ⁻¹) by ring]
        rw [haa, mul_inv_cancel₀ hμ0]]
      simp
    rw [harg]
  ·
    have hQAu : Q (A.val *ᵥ u) = 0 := by rw [hAQ, hu, mul_zero]
    have hwu : polar Q (A.val *ᵥ u) u = 0 := by rw [polar_comm]; exact huAu
    have huAu' : polar Q u (-(A.val *ᵥ u)) = 0 := by
      rw [polar_neg_right, huAu, neg_zero]
    have hswap : eichler Q (A.val *ᵥ u) u = eichler Q u (-(A.val *ᵥ u)) := by
      refine LinearEquiv.ext fun x => ?_
      rw [eichler_apply hQAu hwu, eichler_apply hu huAu']
      rw [QuadraticMap.map_neg, hQAu, polar_neg_right, hu]
      simp only [zero_mul, add_zero, neg_smul, sub_neg_eq_add, smul_neg]
      abel
    have hmu : μ⁻¹ • (A.val *ᵥ (A.val *ᵥ u)) = u := by
      rw [hAAv u, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    refine ⟨u, A.val *ᵥ u, hu0, hu, huAu, hmem, ?_⟩
    rw [hmu]
    exact hswap

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
