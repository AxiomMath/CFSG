module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.PSLForms
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open Matrix

variable {K : Type} [Field K] {n : ℕ}

private lemma exists_mem_notMem_span_of_two_le_finrank {S : Submodule K (Fin n → K)}
    {x : Fin n → K} (hS : 2 ≤ Module.finrank K S) :
    ∃ y ∈ S, y ∉ Submodule.span K {x} := by
  by_contra h
  push Not at h
  have hmono : Module.finrank K S ≤ Module.finrank K (Submodule.span K {x}) :=
    Submodule.finrank_mono fun y hy => h y hy
  have hx : Module.finrank K (Submodule.span K {x}) ≤ 1 := by
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Submodule.span_zero_singleton, finrank_bot]
      exact Nat.zero_le 1
    · rw [finrank_span_singleton hx0]
  omega

private def dotLin {m : ℕ} (φ : Matrix (Fin m) (Fin n) K) : (Fin n → K) →ₗ[K] (Fin m → K) where
  toFun v i := φ i ⬝ᵥ v
  map_add' v v' := by
    ext i
    simp [dotProduct_add]
  map_smul' c v := by
    ext i
    simp

private lemma le_finrank_ker_dotProduct {m : ℕ} (φ : Matrix (Fin m) (Fin n) K) :
    n - m ≤ Module.finrank K (LinearMap.ker (dotLin φ)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (dotLin φ)
  have htop : Module.finrank K (Fin n → K) = n := by simp
  have hle : Module.finrank K (LinearMap.range (dotLin φ)) ≤ m := by
    refine (Submodule.finrank_le _).trans ?_
    simp
  omega

private lemma mem_ker_dotLin {m : ℕ} (φ : Matrix (Fin m) (Fin n) K) (v : Fin n → K) :
    v ∈ LinearMap.ker (dotLin φ) ↔ ∀ i, φ i ⬝ᵥ v = 0 := by
  rw [LinearMap.mem_ker]
  change (fun i => φ i ⬝ᵥ v) = 0 ↔ ∀ i, φ i ⬝ᵥ v = 0
  rw [funext_iff]
  simp

private lemma exists_rankOne_of_left_dependent {w₁ w₂ φ₁ φ₂ : Fin n → K}
    (h11 : φ₁ ⬝ᵥ w₁ = 0) (h21 : φ₂ ⬝ᵥ w₁ = 0) (h22 : φ₂ ⬝ᵥ w₂ = 0)
    (h : ¬ LinearIndependent K ![w₁, w₂]) :
    ∃ w φ : Fin n → K, vecMulVec w₁ φ₁ + vecMulVec w₂ φ₂ = vecMulVec w φ ∧ φ ⬝ᵥ w = 0 := by
  by_cases hw₁ : w₁ = 0
  · exact ⟨w₂, φ₂, by rw [hw₁, Matrix.zero_vecMulVec, zero_add], h22⟩
  · obtain ⟨c, hc⟩ : ∃ c, c • w₁ = w₂ := by
      by_contra hc
      push Not at hc
      exact h ((LinearIndependent.pair_iff' hw₁).mpr hc)
    refine ⟨w₁, φ₁ + c • φ₂, ?_, ?_⟩
    · have h2 : vecMulVec w₂ φ₂ = vecMulVec w₁ (c • φ₂) := by
        rw [← hc, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]
      rw [h2, Matrix.vecMulVec_add]
    · simp [add_dotProduct, smul_dotProduct, h11, h21]

private lemma exists_rankOne_of_right_dependent {w₁ w₂ φ₁ φ₂ : Fin n → K}
    (h11 : φ₁ ⬝ᵥ w₁ = 0) (h12 : φ₁ ⬝ᵥ w₂ = 0) (h22 : φ₂ ⬝ᵥ w₂ = 0)
    (h : ¬ LinearIndependent K ![φ₁, φ₂]) :
    ∃ w φ : Fin n → K, vecMulVec w₁ φ₁ + vecMulVec w₂ φ₂ = vecMulVec w φ ∧ φ ⬝ᵥ w = 0 := by
  by_cases hφ₁ : φ₁ = 0
  · exact ⟨w₂, φ₂, by rw [hφ₁, Matrix.vecMulVec_zero, zero_add], h22⟩
  · obtain ⟨c, hc⟩ : ∃ c, c • φ₁ = φ₂ := by
      by_contra hc
      push Not at hc
      exact h ((LinearIndependent.pair_iff' hφ₁).mpr hc)
    refine ⟨w₁ + c • w₂, φ₁, ?_, ?_⟩
    · have h3 : vecMulVec w₂ φ₂ = vecMulVec (c • w₂) φ₁ := by
        rw [← hc, Matrix.vecMulVec_smul, Matrix.smul_vecMulVec]
      rw [h3, ← Matrix.add_vecMulVec]
    · rw [dotProduct_add, dotProduct_smul, h11, h12, smul_zero, add_zero]

private lemma exists_rankOne_of_not_independent {w₁ w₂ φ₁ φ₂ : Fin n → K}
    (h11 : φ₁ ⬝ᵥ w₁ = 0) (h12 : φ₁ ⬝ᵥ w₂ = 0)
    (h21 : φ₂ ⬝ᵥ w₁ = 0) (h22 : φ₂ ⬝ᵥ w₂ = 0)
    (h : ¬ (LinearIndependent K ![w₁, w₂] ∧ LinearIndependent K ![φ₁, φ₂])) :
    ∃ w φ : Fin n → K, vecMulVec w₁ φ₁ + vecMulVec w₂ φ₂ = vecMulVec w φ ∧ φ ⬝ᵥ w = 0 := by
  rw [not_and_or] at h
  rcases h with hw | hφ
  · exact exists_rankOne_of_left_dependent h11 h21 h22 hw
  · exact exists_rankOne_of_right_dependent h11 h12 h22 hφ

private lemma exists_frame_of_vecMulVec (hn : 4 ≤ n) {w φ : Fin n → K} (hw : w ≠ 0)
    (hφ : φ ≠ 0) :
    ∃ w₂ φ₂ : Fin n → K, LinearIndependent K ![w, w₂] ∧
      LinearIndependent K ![φ, φ₂] ∧ φ ⬝ᵥ w₂ = 0 ∧ φ₂ ⬝ᵥ w = 0 ∧ φ₂ ⬝ᵥ w₂ = 0 := by
  have h1 : 2 ≤ Module.finrank K (LinearMap.ker (dotLin (fun _ : Fin 1 => φ))) := by
    have h := le_finrank_ker_dotProduct (m := 1) (fun _ : Fin 1 => φ)
    omega
  obtain ⟨w₂, hw₂, hw₂span⟩ := exists_mem_notMem_span_of_two_le_finrank h1
  have hφw₂ : φ ⬝ᵥ w₂ = 0 := by
    have h := (mem_ker_dotLin (fun _ : Fin 1 => φ) w₂).mp hw₂ (0 : Fin 1)
    simpa using h
  have hindW : LinearIndependent K ![w, w₂] := by
    rw [LinearIndependent.pair_iff' hw]
    intro c hc
    apply hw₂span
    rw [← hc]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self w)
  have h2 : 2 ≤ Module.finrank K (LinearMap.ker (dotLin ![w, w₂])) := by
    have h := le_finrank_ker_dotProduct (m := 2) ![w, w₂]
    omega
  obtain ⟨φ₂, hφ₂, hφ₂span⟩ :=
    exists_mem_notMem_span_of_two_le_finrank (x := φ) h2
  have hmem := (mem_ker_dotLin ![w, w₂] φ₂).mp hφ₂
  have hwφ₂ : w ⬝ᵥ φ₂ = 0 := by simpa using hmem 0
  have hw₂φ₂ : w₂ ⬝ᵥ φ₂ = 0 := by simpa using hmem 1
  refine ⟨w₂, φ₂, hindW, ?_, hφw₂, ?_, ?_⟩
  · rw [LinearIndependent.pair_iff' hφ]
    intro c hc
    apply hφ₂span
    rw [← hc]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self φ)
  · rw [dotProduct_comm]
    exact hwφ₂
  · rw [dotProduct_comm]
    exact hw₂φ₂

theorem exists_frame_of_isRankTwoSqZero (hn : 4 ≤ n) {N : Matrix (Fin n) (Fin n) K}
    (hN0 : N ≠ 0) (hN : IsRankTwoSqZero N) :
    ∃ (w₁ w₂ φ₁ φ₂ : Fin n → K) (a b : K), LinearIndependent K ![w₁, w₂] ∧
      LinearIndependent K ![φ₁, φ₂] ∧ φ₁ ⬝ᵥ w₁ = 0 ∧ φ₁ ⬝ᵥ w₂ = 0 ∧ φ₂ ⬝ᵥ w₁ = 0 ∧
      φ₂ ⬝ᵥ w₂ = 0 ∧ N = a • vecMulVec w₁ φ₁ + b • vecMulVec w₂ φ₂ := by
  obtain ⟨w₁, w₂, φ₁, φ₂, h11, h12, h21, h22, hN'⟩ := hN
  by_cases hind : LinearIndependent K ![w₁, w₂] ∧ LinearIndependent K ![φ₁, φ₂]
  · exact ⟨w₁, w₂, φ₁, φ₂, 1, 1, hind.1, hind.2, h11, h12, h21, h22, by
      rw [hN', one_smul, one_smul]⟩
  · obtain ⟨w, φ, hwφ, hφw⟩ := exists_rankOne_of_not_independent h11 h12 h21 h22 hind
    have hvec0 : vecMulVec w φ ≠ 0 := by rw [← hwφ, ← hN']; exact hN0
    have hw0 : w ≠ 0 := by
      intro hw
      exact hvec0 (by rw [hw, Matrix.zero_vecMulVec])
    have hφ0 : φ ≠ 0 := by
      intro hφ
      exact hvec0 (by rw [hφ, Matrix.vecMulVec_zero])
    obtain ⟨w₂, φ₂, hindW, hindΦ, hφw₂, hφ₂w, hφ₂w₂⟩ :=
      exists_frame_of_vecMulVec hn hw0 hφ0
    exact ⟨w, w₂, φ, φ₂, 1, 0, hindW, hindΦ, hφw, hφw₂, hφ₂w, hφ₂w₂, by
      rw [hN', hwφ, one_smul, zero_smul, add_zero]⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
