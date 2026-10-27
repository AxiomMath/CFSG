module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
import Mathlib.LinearAlgebra.Eigenspace.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem exists_eichler_inv_skewSquare (hK2 : ringChar K ≠ 2) (hd : 3 ≤ d) {A : GL (Fin d) K}
    {μ l : K} (hl0 : l ≠ 0) (hAQ : ∀ v, Q (A.val *ᵥ v) = μ * Q v)
    (hAA : A.val * A.val = (l ^ 2) • 1) (hμ : μ = -l ^ 2) :
    ∃ u w : Fin d → K, u ≠ 0 ∧ Q u = 0 ∧ polar Q u w = 0 ∧ w ∉ Submodule.span K {u} ∧
      eichler Q (A.val *ᵥ u) (μ⁻¹ • (A.val *ᵥ w)) = eichler Q u (-w) := by
  classical
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl0
  have hB : ∀ x y : Fin d → K, polar Q (A.val *ᵥ x) (A.val *ᵥ y) = μ * polar Q x y := by
    intro x y
    unfold QuadraticMap.polar
    rw [← Matrix.mulVec_add, hAQ, hAQ, hAQ]
    ring
  let f : Module.End K (Fin d → K) := Matrix.mulVecLin A.val
  have hf : ∀ v, f v = A.val *ᵥ v := fun v => Matrix.mulVecLin_apply A.val v
  have hmul : ∀ v, A.val *ᵥ (A.val *ᵥ v) = (l ^ 2) • v := by
    intro v
    rw [Matrix.mulVec_mulVec, hAA, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hsing : ∀ (ε : K), ε ^ 2 = l ^ 2 → ∀ x ∈ f.eigenspace ε, Q x = 0 := by
    intro ε hε x hx
    have hx' : f x = ε • x := Module.End.mem_eigenspace_iff.mp hx
    have h1 : μ * Q x = ε ^ 2 * Q x := by
      calc μ * Q x = Q (A.val *ᵥ x) := (hAQ x).symm
        _ = Q (f x) := by rw [hf]
        _ = Q (ε • x) := by rw [hx']
        _ = ε ^ 2 * Q x := map_smul_eq_sq Q ε x
    rw [hε, hμ] at h1
    have h0 : (2 * l ^ 2) * Q x = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero h2 hl2)
  have horth : ∀ (ε : K), ε ^ 2 = l ^ 2 → ∀ x ∈ f.eigenspace ε, ∀ y ∈ f.eigenspace ε,
      polar Q x y = 0 := by
    intro ε hε x hx y hy
    have hx' : f x = ε • x := Module.End.mem_eigenspace_iff.mp hx
    have hy' : f y = ε • y := Module.End.mem_eigenspace_iff.mp hy
    have h1 : μ * polar Q x y = ε ^ 2 * polar Q x y := by
      calc μ * polar Q x y = polar Q (A.val *ᵥ x) (A.val *ᵥ y) :=
            (hB x y).symm
        _ = polar Q (f x) (f y) := by simp only [hf]
        _ = polar Q (ε • x) (ε • y) := by rw [hx', hy']
        _ = ε * (ε * polar Q x y) := by rw [polar_smul_left_eq, polar_smul_right_eq]
        _ = ε ^ 2 * polar Q x y := by ring
    rw [hε, hμ] at h1
    have h0 : (2 * l ^ 2) * polar Q x y = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero h2 hl2)
  have hsup : f.eigenspace l ⊔ f.eigenspace (-l) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hmeml : f (A.val *ᵥ v + l • v) = l • (A.val *ᵥ v + l • v) := by
      rw [map_add, map_smul, hf, hf, hmul, smul_add, smul_smul, pow_two, add_comm]
    have hmemm : f (A.val *ᵥ v - l • v) = (-l) • (A.val *ᵥ v - l • v) := by
      rw [map_sub, map_smul, hf, hf, hmul, smul_sub, smul_smul, pow_two]
      module
    have hdecomp : (A.val *ᵥ v + l • v) - (A.val *ᵥ v - l • v) = (2 * l) • v := by
      module
    have h2l : (2 : K) * l ≠ 0 := mul_ne_zero h2 hl0
    have hv : v = (2 * l)⁻¹ • ((A.val *ᵥ v + l • v) - (A.val *ᵥ v - l • v)) := by
      rw [hdecomp, smul_smul, inv_mul_cancel₀ h2l, one_smul]
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.mem_sup_left (Module.End.mem_eigenspace_iff.mpr hmeml))
      (Submodule.mem_sup_right (Module.End.mem_eigenspace_iff.mpr hmemm)))
  have hdim : 2 ≤ Module.finrank K (f.eigenspace l) ∨
      2 ≤ Module.finrank K (f.eigenspace (-l)) := by
    by_contra h
    rw [not_or] at h
    obtain ⟨h1, h2'⟩ := h
    have hle := Submodule.finrank_sup_add_finrank_inf_eq (f.eigenspace l) (f.eigenspace (-l))
    rw [hsup, finrank_top, Module.finrank_fin_fun] at hle
    omega
  obtain ⟨ε, hε2, hεfin⟩ :
      ∃ ε : K, ε ^ 2 = l ^ 2 ∧ 2 ≤ Module.finrank K (f.eigenspace ε) := by
    rcases hdim with h | h
    · exact ⟨l, by ring, h⟩
    · exact ⟨-l, by ring, h⟩
  have hne : f.eigenspace ε ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hεfin
    omega
  obtain ⟨u, huE, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hnotle : ¬ f.eigenspace ε ≤ Submodule.span K {u} := by
    intro hle
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hu0] at h1
    omega
  obtain ⟨w, hwE, hwspan⟩ := SetLike.not_le_iff_exists.mp hnotle
  refine ⟨u, w, hu0, hsing ε hε2 u huE, horth ε hε2 u huE w hwE, hwspan, ?_⟩
  have hAu : A.val *ᵥ u = ε • u := by
    rw [← hf]; exact Module.End.mem_eigenspace_iff.mp huE
  have hAw : A.val *ᵥ w = ε • w := by
    rw [← hf]; exact Module.End.mem_eigenspace_iff.mp hwE
  rw [hAu, hAw, eichler_smul_left]
  have hcoef : ε * μ⁻¹ * ε = -1 := by
    have hεε : ε * ε = l ^ 2 := by rw [← pow_two, hε2]
    calc ε * μ⁻¹ * ε = (ε * ε) * μ⁻¹ := by ring
      _ = l ^ 2 * μ⁻¹ := by rw [hεε]
      _ = -1 := by rw [hμ, inv_neg, mul_neg, mul_inv_cancel₀ hl2]
  rw [smul_smul, smul_smul, hcoef, neg_one_smul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
