module

import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open QuadraticMap

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

private theorem exists_polar_eq_one_of_notMem_span_three {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] {Q : QuadraticForm k V}
    (hQ : (polarBilin Q).Nondegenerate) {u₁ u₂ z₁ z : V}
    (hz : z ∉ Submodule.span k {u₁, u₂, z₁}) :
    ∃ y : V, polar Q u₁ y = 0 ∧ polar Q u₂ y = 0 ∧ polar Q z₁ y = 0 ∧ polar Q z y = 1 := by
  classical
  obtain ⟨f, hfz, hle⟩ := Submodule.exists_le_ker_of_notMem hz
  let g : V →ₗ[k] k := (f z)⁻¹ • f
  have hgz : g z = 1 := by
    rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hfz]
  have hgu₁ : g u₁ = 0 := by
    have h : f u₁ = 0 := LinearMap.mem_ker.mp (hle (Submodule.subset_span (by simp)))
    rw [LinearMap.smul_apply, smul_eq_mul, h, mul_zero]
  have hgu₂ : g u₂ = 0 := by
    have h : f u₂ = 0 := LinearMap.mem_ker.mp (hle (Submodule.subset_span (by simp)))
    rw [LinearMap.smul_apply, smul_eq_mul, h, mul_zero]
  have hgz₁ : g z₁ = 0 := by
    have h : f z₁ = 0 := LinearMap.mem_ker.mp (hle (Submodule.subset_span (by simp)))
    rw [LinearMap.smul_apply, smul_eq_mul, h, mul_zero]
  let y : V := (LinearMap.BilinForm.toDual (polarBilin Q) hQ).symm g
  have happly : ∀ v : V, polar Q y v = g v := by
    intro v
    rw [← QuadraticMap.polarBilin_apply_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
  exact ⟨y, by rw [polar_comm Q u₁ y, happly, hgu₁],
    by rw [polar_comm Q u₂ y, happly, hgu₂],
    by rw [polar_comm Q z₁ y, happly, hgz₁],
    by rw [polar_comm Q z y, happly, hgz]⟩

theorem exists_heis_partner (hQ : (polarBilin Q).Nondegenerate) (hd : 7 ≤ d)
    {u₁ u₂ z₁ z₂ y₁ : Fin d → K} (hy₁ : polar Q u₁ y₁ = 0) (hy₂ : polar Q u₂ y₁ = 0)
    (hzy : polar Q z₁ y₁ = 1) :
    ∃ z₃ y₂ : Fin d → K, polar Q u₁ z₃ = 0 ∧ polar Q u₂ z₃ = 0 ∧ polar Q u₁ y₂ = 0 ∧
      polar Q u₂ y₂ = 0 ∧ polar Q z₃ y₂ = 1 ∧ polar Q z₂ z₃ = 0 ∧ polar Q y₁ z₃ = 0 ∧
      polar Q z₁ y₂ = 0 := by
  classical
  let f : (Fin d → K) →ₗ[K] (K × K) × (K × K) :=
    ((polarBilin Q u₁).prod (polarBilin Q u₂)).prod
      ((polarBilin Q z₂).prod (polarBilin Q y₁))
  let W : Submodule K (Fin d → K) := LinearMap.ker f
  have hWmem : ∀ x : Fin d → K, x ∈ W ↔ polar Q u₁ x = 0 ∧ polar Q u₂ x = 0 ∧
      polar Q z₂ x = 0 ∧ polar Q y₁ x = 0 := by
    intro x
    simp [W, f, LinearMap.mem_ker, polarBilin_apply_apply, and_assoc]
  have hVdim : Module.finrank K (Fin d → K) = d := Module.finrank_fin_fun K
  have hWdim : d - 4 ≤ Module.finrank K W := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    rw [hVdim] at h
    have hrange : Module.finrank K (LinearMap.range f) ≤ 4 := by
      have hle := Submodule.finrank_le (LinearMap.range f)
      have hcd : Module.finrank K ((K × K) × (K × K)) = 4 := by
        simp [Module.finrank_prod, Module.finrank_self]
      rwa [hcd] at hle
    have hker : Module.finrank K W = Module.finrank K (LinearMap.ker f) := rfl
    omega
  have hWorth : ∀ x ∈ W, polar Q y₁ x = 0 := fun x hx => ((hWmem x).mp hx).2.2.2
  have hWT : W ⊓ Submodule.span K ({u₁, u₂, z₁} : Set (Fin d → K)) ≤
      Submodule.span K ({u₁, u₂} : Set (Fin d → K)) := by
    intro x hx
    obtain ⟨hxW, hxT⟩ := Submodule.mem_inf.mp hx
    obtain ⟨a, b, c, habc⟩ := Submodule.mem_span_triple.mp hxT
    have hx0 : polar Q y₁ x = 0 := hWorth x hxW
    have hc : c = 0 := by
      have h1 : polar Q y₁ x = c := by
        rw [← habc]
        simp only [polar_add_right, polar_smul_right, smul_eq_mul, polar_comm Q y₁ u₁,
          polar_comm Q y₁ u₂, polar_comm Q y₁ z₁, hy₁, hy₂, hzy]
        ring
      rw [h1] at hx0
      exact hx0
    have hx' : a • u₁ + b • u₂ = x := by
      calc a • u₁ + b • u₂ = a • u₁ + b • u₂ + c • z₁ := by simp [hc]
        _ = x := habc
    exact Submodule.mem_span_pair.mpr ⟨a, b, hx'⟩
  let T : Submodule K (Fin d → K) := Submodule.span K ({u₁, u₂, z₁} : Set (Fin d → K))
  have hspan2 : Module.finrank K (Submodule.span K ({u₁, u₂} : Set (Fin d → K))) ≤ 2 := by
    have hle := finrank_span_le_card (R := K) ({u₁, u₂} : Set (Fin d → K))
    have h2 : ({u₁, u₂} : Set (Fin d → K)).toFinset.card ≤ 2 := by
      rw [Set.toFinset_insert, Set.toFinset_singleton]
      exact Finset.card_insert_le _ _
    omega
  have hWinf : Module.finrank K ↥(W ⊓ T) ≤ 2 :=
    le_trans (Submodule.finrank_mono hWT) hspan2
  have hnotle : ¬ W ≤ T := by
    intro hle
    have hinf : W ⊓ T = W := inf_eq_left.mpr hle
    have hW2 : Module.finrank K W ≤ 2 := by
      rw [← hinf]
      exact hWinf
    omega
  obtain ⟨z₃, hz₃W, hz₃T⟩ : ∃ z₃ : Fin d → K, z₃ ∈ W ∧ z₃ ∉ T := by
    by_contra h
    exact hnotle fun x hx => by
      by_contra hxT
      exact h ⟨x, hx, hxT⟩
  obtain ⟨hz₃u₁, hz₃u₂, hz₃z₂, hz₃y₁⟩ := (hWmem z₃).mp hz₃W
  obtain ⟨y₂, hy₂u₁, hy₂u₂, hy₂z₁, hy₂z₃⟩ :=
    exists_polar_eq_one_of_notMem_span_three (Q := Q) hQ (u₁ := u₁) (u₂ := u₂)
      (z₁ := z₁) (z := z₃) hz₃T
  exact ⟨z₃, y₂, hz₃u₁, hz₃u₂, hy₂u₁, hy₂u₂, hy₂z₃, hz₃z₂, hz₃y₁, hy₂z₁⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
