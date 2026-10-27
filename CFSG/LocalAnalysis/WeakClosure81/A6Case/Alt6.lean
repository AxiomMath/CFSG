module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.RankThree.PartOne.N1322.CaseA6

public section

namespace CFSG.LocalAnalysis.WeakClosure81.A6Case

open Equiv Equiv.Perm

private def s₀ : alternatingGroup (Fin 6) :=
  ⟨swap 1 2 * swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def p₁₀ : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def p₂₀ : alternatingGroup (Fin 6) :=
  ⟨swap 3 4 * swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private theorem s₀_mul_self : s₀ * s₀ = 1 := by decide

private theorem s₀_ne_one : s₀ ≠ 1 := by decide

private theorem p₁₀_pow_three : p₁₀ ^ 3 = 1 := by decide

private theorem p₂₀_pow_three : p₂₀ ^ 3 = 1 := by decide

private theorem p₁₀_ne_one : p₁₀ ≠ 1 := by decide

private theorem p₁₀_commute_p₂₀ : Commute p₁₀ p₂₀ := by
  show p₁₀ * p₂₀ = p₂₀ * p₁₀
  decide

private theorem s₀_inverts_p₁₀ : s₀ * p₁₀ * s₀⁻¹ = p₁₀⁻¹ := by decide

private theorem s₀_inverts_p₂₀ : s₀ * p₂₀ * s₀⁻¹ = p₂₀⁻¹ := by decide

private theorem p₁₀_orderOf : orderOf p₁₀ = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact orderOf_eq_prime p₁₀_pow_three p₁₀_ne_one

private theorem p₂₀_notMem_zpowers : p₂₀ ∉ Subgroup.zpowers p₁₀ := by
  rw [mem_zpowers_iff_mem_range_orderOf, p₁₀_orderOf]
  simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
  intro i hi hpi
  interval_cases i <;> exact absurd hpi (by decide)

theorem exists_inverted_pair (s : alternatingGroup (Fin 6)) (hs : s * s = 1) (hs1 : s ≠ 1) :
    ∃ p₁ p₂ : alternatingGroup (Fin 6), p₁ ^ 3 = 1 ∧ p₂ ^ 3 = 1 ∧ p₁ ≠ 1 ∧ Commute p₁ p₂ ∧
      s * p₁ * s⁻¹ = p₁⁻¹ ∧ s * p₂ * s⁻¹ = p₂⁻¹ ∧ p₂ ∉ Subgroup.zpowers p₁ := by
  obtain ⟨k, hk⟩ := CFSG.RankThree.PartOne.N1322.A6_conj s₀ s s₀_mul_self s₀_ne_one hs hs1
  set φ : alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6) := MulAut.conj k with hφ
  have hφs : φ s₀ = s := by
    rw [hφ, MulAut.conj_apply]
    exact hk
  refine ⟨φ p₁₀, φ p₂₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, p₁₀_pow_three, map_one]
  · rw [← map_pow, p₂₀_pow_three, map_one]
  · exact fun h => p₁₀_ne_one (φ.injective (by rw [h, map_one]))
  · show φ p₁₀ * φ p₂₀ = φ p₂₀ * φ p₁₀
    rw [← map_mul, ← map_mul, p₁₀_commute_p₂₀]
  · rw [← hφs]
    show φ s₀ * φ p₁₀ * (φ s₀)⁻¹ = (φ p₁₀)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, s₀_inverts_p₁₀, map_inv]
  · rw [← hφs]
    show φ s₀ * φ p₂₀ * (φ s₀)⁻¹ = (φ p₂₀)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, s₀_inverts_p₂₀, map_inv]
  · intro h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
    exact p₂₀_notMem_zpowers (Subgroup.mem_zpowers_iff.mpr ⟨n, φ.injective (by rw [map_zpow, hn])⟩)

end CFSG.LocalAnalysis.WeakClosure81.A6Case
