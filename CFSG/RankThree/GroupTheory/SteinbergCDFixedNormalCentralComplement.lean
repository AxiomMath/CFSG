module

public import CFSG.RankThree.Coprime.SolvableFixedCommutator

public section

namespace CFSG.RankThree.GroupTheory

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

theorem coprime_fixed_normal_subgroup_central_complement {K A : Type*} [Group K] [Group A]
    [Finite K] [Finite A] [MulDistribMulAction A K] (hK : Group.IsSolvable K)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A)) (N P : Subgroup K) [N.Normal]
    (hP : P ≤ center K) (hPinv : ∀ a : A, ∀ x ∈ P, a • x ∈ P)
    (hNfix : ∀ a : A, ∀ x ∈ N, a • x = x) (hC : centralizer (N : Set K) ≤ N ⊔ P) :
    actionCommutator A (⊤ : Subgroup K) ≤ P ∧
      (∀ k : K, ∃ x ∈ P, ∃ c ∈ CFSG.fixedPointSubgroup A K, k = x * c) ∧
      (∀ k : K, ∃ z ∈ center K, ∃ c ∈ CFSG.fixedPointSubgroup A K, k = z * c) := by
  obtain ⟨-, -, hfac, hidem⟩ :=
    CFSG.RankThree.Coprime.solvable_coprime_fixed_commutator_factorization (A := A) hK hcop
  set D := actionCommutator A (⊤ : Subgroup K) with hD
  have hDC : D ≤ centralizer (N : Set K) := by
    refine (closure_le _).mpr ?_
    rintro _ ⟨k, -, a, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro n hn
    have hkn : k * n * k⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem n hn k
    have h1 : a • (k * n * k⁻¹) = k * n * k⁻¹ := hNfix a _ hkn
    rw [smul_mul', smul_mul', smul_inv', hNfix a n hn] at h1
    calc n * (k⁻¹ * (a • k)) = k⁻¹ * (k * n * k⁻¹) * (a • k) := by group
      _ = k⁻¹ * ((a • k) * n * (a • k)⁻¹) * (a • k) := by rw [h1]
      _ = k⁻¹ * (a • k) * n := by group
  have hPn : P.Normal := normal_of_le_center hP
  have hNP : actionCommutator A (N ⊔ P) ≤ P := by
    refine (closure_le _).mpr ?_
    rintro _ ⟨x, hx, a, rfl⟩
    have hx' : x ∈ ((N : Set K) * (P : Set K)) := by
      rw [← mul_normal N P]
      exact hx
    obtain ⟨n, hn, q, hq, rfl⟩ := hx'
    rw [SetLike.mem_coe]
    have h : (n * q)⁻¹ * (a • (n * q)) = q⁻¹ * (a • q) := by
      rw [smul_mul', hNfix a n hn]
      group
    rw [h]
    exact mul_mem (inv_mem hq) (hPinv a q hq)
  have hDP : D ≤ P := by
    rw [← hidem]
    have hmono : actionCommutator A D ≤ actionCommutator A (N ⊔ P) :=
      closure_mono fun _ ⟨x, hx, a, hxa⟩ => ⟨x, hC (hDC hx), a, hxa⟩
    exact hmono.trans hNP
  refine ⟨hDP, fun k => ?_, fun k => ?_⟩
  · obtain ⟨d, hd, c, hc, rfl⟩ := hfac k
    exact ⟨d, hDP hd, c, hc, rfl⟩
  · obtain ⟨d, hd, c, hc, rfl⟩ := hfac k
    exact ⟨d, hP (hDP hd), c, hc, rfl⟩

end CFSG.RankThree.GroupTheory
