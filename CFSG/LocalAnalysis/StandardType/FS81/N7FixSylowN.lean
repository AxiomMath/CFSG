module

public import CFSG.LocalAnalysis.StandardType.FS81.N7FixSylowA

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

private lemma q2nN7_neg_eq_self_zmod3 : ∀ a : ZMod 3, -a = a → a = 0 := by decide

private lemma q2nN7_exists_ne_zero_ne {i : Fin 8} (hi : i ≠ 0) :
    ∃ j : Fin 8, j ≠ 0 ∧ j ≠ i := by
  by_cases h : i = 1
  · exact ⟨2, by decide, by rw [h]; decide⟩
  · exact ⟨1, by decide, fun hji => h hji.symm⟩

namespace N7Setup

variable {X : Type} [Group X] [Finite X] (S : N7Setup X)

theorem q2nN7_conj_sgn {h : X} (hh : h ∈ S.H) {f : X} {A : Finset (Fin 8)}
    (hf : S.ρ f = sgn A) :
    ∃ σ : Equiv.Perm (Fin 8), σ 0 = 0 ∧ S.ρ (h * f * h⁻¹) = sgn (A.map σ.toEmbedding) := by
  obtain ⟨σ, s, -, ⟨hσ0, -, -⟩, hsp⟩ := (S.mem_H_iff h).1 hh
  refine ⟨σ, hσ0, ?_⟩
  have hleft : S.ρ h * S.ρ h⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hsinv : spMat σ s * S.ρ h⁻¹ = 1 := by
    rw [← hsp]
    exact hleft
  calc S.ρ (h * f * h⁻¹) = S.ρ h * S.ρ f * S.ρ h⁻¹ := by
        rw [map_mul, map_mul]
    _ = spMat σ s * sgn A * S.ρ h⁻¹ := by rw [hsp, hf]
    _ = (sgn (A.map σ.toEmbedding) * spMat σ s) * S.ρ h⁻¹ := by
        rw [q2nN7_spMat_mul_sgn]
    _ = sgn (A.map σ.toEmbedding) * (spMat σ s * S.ρ h⁻¹) := by rw [mul_assoc]
    _ = sgn (A.map σ.toEmbedding) := by rw [hsinv, mul_one]

theorem conj_mem_F1 {h : X} (hh : h ∈ S.H) {f : X} (hf : f ∈ S.F1) : h * f * h⁻¹ ∈ S.F1 := by
  obtain ⟨A, h0, he, hA⟩ := (S.mem_F1_iff f).1 hf
  obtain ⟨σ, hσ0, hconj⟩ := S.q2nN7_conj_sgn hh hA
  rw [S.mem_F1_iff]
  refine ⟨A.map σ.toEmbedding, ?_, ?_, hconj⟩
  · intro hmem
    rw [Finset.mem_map_equiv] at hmem
    rw [show σ.symm 0 = 0 from (Equiv.symm_apply_eq σ).2 hσ0.symm] at hmem
    exact h0 hmem
  · rw [Finset.card_map]
    exact he

theorem eq_smul_e0_of_fixed {v : Fin 8 → ZMod 3} (hv : ∀ f ∈ S.F1, S.ρ f *ᵥ v = v) :
    ∃ c : ZMod 3, v = c • e0 := by
  have hzero : ∀ i : Fin 8, i ≠ 0 → v i = 0 := by
    intro i hi
    obtain ⟨j, hj0, hji⟩ := q2nN7_exists_ne_zero_ne hi
    have h0 : (0 : Fin 8) ∉ ({i, j} : Finset (Fin 8)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hi h.symm, fun h => hj0 h.symm⟩
    have hcard : ({i, j} : Finset (Fin 8)).card = 2 := Finset.card_pair hji.symm
    have hfix : sgn ({i, j} : Finset (Fin 8)) ∈ evenFix0 7 :=
      q2nN7_sgn_mem_evenFix0 h0 (by rw [hcard]; decide)
    obtain ⟨f, hfρ⟩ := S.surj_H _ hfix
    have hfF1 : f ∈ S.F1 :=
      (S.mem_F1_iff f).2 ⟨{i, j}, h0, by rw [hcard]; decide, hfρ⟩
    have hfixv : sgn ({i, j} : Finset (Fin 8)) *ᵥ v = v := by
      have := hv f hfF1
      rwa [hfρ] at this
    have hcoord : (fun i => if i ∈ ({i, j} : Finset (Fin 8)) then -v i else v i) i = v i := by
      simpa only [q2nN7_sgn_mulVec] using congrFun hfixv i
    have hnegi : -v i = v i := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hcoord
    exact q2nN7_neg_eq_self_zmod3 (v i) hnegi
  refine ⟨v 0, ?_⟩
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [e0]
  · have hvi : v i = 0 := hzero i hi
    simp [e0, hvi, Pi.single_apply, hi]

theorem normalizer_F1 : Subgroup.normalizer (S.F1 : Set X) = S.H := by
  apply le_antisymm
  · intro y hy
    have hyiff : ∀ h, h ∈ S.F1 ↔ y * h * y⁻¹ ∈ S.F1 :=
      (Subgroup.mem_normalizer_iff (H := S.F1)).1 hy
    have hv : ∀ f ∈ S.F1, S.ρ f *ᵥ (S.ρ y *ᵥ e0) = S.ρ y *ᵥ e0 := by
      intro f hf
      have hyconj : y⁻¹ * f * y ∈ S.F1 := by
        refine (hyiff (y⁻¹ * f * y)).2 ?_
        have h1 : y * (y⁻¹ * f * y) * y⁻¹ = f := by group
        rw [h1]
        exact hf
      have hH : y⁻¹ * f * y ∈ S.H := S.F1_le_H hyconj
      have hfix : S.ρ (y⁻¹ * f * y) *ᵥ e0 = e0 := hH
      calc S.ρ f *ᵥ (S.ρ y *ᵥ e0) = (S.ρ f * S.ρ y) *ᵥ e0 := by
            rw [Matrix.mulVec_mulVec]
        _ = S.ρ (f * y) *ᵥ e0 := by rw [map_mul]
        _ = S.ρ (y * (y⁻¹ * f * y)) *ᵥ e0 := by
            rw [show f * y = y * (y⁻¹ * f * y) from by group]
        _ = (S.ρ y * S.ρ (y⁻¹ * f * y)) *ᵥ e0 := by rw [map_mul]
        _ = S.ρ y *ᵥ (S.ρ (y⁻¹ * f * y) *ᵥ e0) := by rw [Matrix.mulVec_mulVec]
        _ = S.ρ y *ᵥ e0 := by rw [hfix]
    obtain ⟨c, hc⟩ := S.eq_smul_e0_of_fixed (v := S.ρ y *ᵥ e0) hv
    exact (S.mem_H_iff y).2 ((S.norm_iff y).2 ⟨c, hc⟩)
  · intro h hh
    refine (Subgroup.mem_normalizer_iff (H := S.F1)).2 ?_
    intro f
    constructor
    · intro hf
      exact S.conj_mem_F1 hh hf
    · intro hf
      have hh' : h⁻¹ ∈ S.H := S.H.inv_mem hh
      have hconj : h⁻¹ * (h * f * h⁻¹) * (h⁻¹)⁻¹ ∈ S.F1 := S.conj_mem_F1 hh' hf
      rwa [show h⁻¹ * (h * f * h⁻¹) * (h⁻¹)⁻¹ = f from by group] at hconj

end N7Setup

end CFSG.StandardType.FrameRoute.FS81

end
