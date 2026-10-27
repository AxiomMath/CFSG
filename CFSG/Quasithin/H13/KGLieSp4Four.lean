module

public import CFSG.Quasithin.H13.KGLieSL3Four

public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

section Sp4

variable {K : Type} [Field K]

abbrev spJ (K : Type) [Field K] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks 0 1 (-1) 0

@[expose] def spT (y : Fin 2 ⊕ Fin 2 → K) (c : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  1 + c • Matrix.vecMulVec y (y ᵥ* spJ K)

theorem spT_mulVec (y : Fin 2 ⊕ Fin 2 → K) (c : K) (z : Fin 2 ⊕ Fin 2 → K) :
    spT y c *ᵥ z = z + (c * (y ⬝ᵥ (spJ K *ᵥ z))) • y := by
  funext k
  rcases k with k | k <;> fin_cases k <;>
    simp [spT, Matrix.mulVec, Matrix.vecMul, Matrix.vecMulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.one_apply, Matrix.fromBlocks] <;> ring

theorem spT_mul (y : Fin 2 ⊕ Fin 2 → K) (a b : K) : spT y a * spT y b = spT y (a + b) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [spT, Matrix.mul_apply, Matrix.vecMul, Matrix.vecMulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.one_apply, Matrix.fromBlocks] <;> ring

theorem spT_zero (y : Fin 2 ⊕ Fin 2 → K) : spT y 0 = 1 := by
  rw [spT, zero_smul, add_zero]

theorem spT_symp (y : Fin 2 ⊕ Fin 2 → K) (c : K) : (spT y c)ᵀ * spJ K * spT y c = spJ K := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [spT, Matrix.mul_apply, Matrix.vecMul, Matrix.vecMulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.one_apply, Matrix.fromBlocks] <;> ring

theorem exists_pairTrace_sp4 [Finite K] (hK : Nat.card K = 4) (u₀ : Fin 2 ⊕ Fin 2 → K)
    (φ : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] K) (hu : u₀ ≠ 0) (hφ : φ ≠ 0) (hφu : φ u₀ = 0) :
    ∃ γ : ↥(StatedSp 2 K), pairTrace φ u₀ γ ^ 2 + pairTrace φ u₀ γ + 1 = 0 := by
  classical
  have : CharP K 2 := charP_two_of_card_four hK
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hB1 : ∃ y : Fin 2 ⊕ Fin 2 → K, y ⬝ᵥ (spJ K *ᵥ u₀) ≠ 0 := by
    obtain ⟨k, hk⟩ : ∃ k, u₀ k ≠ 0 := by
      by_contra h
      push Not at h
      exact hu (funext h)
    rcases k with i | i
    · refine ⟨Pi.single (Sum.inr i) 1, ?_⟩
      fin_cases i <;>
        simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
          Matrix.fromBlocks, Pi.single_apply] using hk
    · refine ⟨Pi.single (Sum.inl i) 1, ?_⟩
      fin_cases i <;>
        simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
          Matrix.fromBlocks, Pi.single_apply] using hk
  have hB2 : ∃ y : Fin 2 ⊕ Fin 2 → K, φ y ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (LinearMap.ext h)
  obtain ⟨y, hyB, hyφ⟩ : ∃ y : Fin 2 ⊕ Fin 2 → K, y ⬝ᵥ (spJ K *ᵥ u₀) ≠ 0 ∧ φ y ≠ 0 := by
    obtain ⟨y₁, hy₁⟩ := hB1
    obtain ⟨y₂, hy₂⟩ := hB2
    by_cases h1 : φ y₁ = 0
    · by_cases h3 : y₂ ⬝ᵥ (spJ K *ᵥ u₀) = 0
      · refine ⟨y₁ + y₂, ?_, ?_⟩
        · rw [add_dotProduct, h3, add_zero]
          exact hy₁
        · rw [map_add, h1, zero_add]
          exact hy₂
      · exact ⟨y₂, h3, hy₂⟩
    · exact ⟨y₁, hy₁, h1⟩
  obtain ⟨ω, hω⟩ := exists_omega hK
  set d := y ⬝ᵥ (spJ K *ᵥ u₀) * φ y with hd'
  have hd : d ≠ 0 := mul_ne_zero hyB hyφ
  set c := ω * d⁻¹ with hc
  have hcd : c * d = ω := by rw [hc, mul_assoc, inv_mul_cancel₀ hd, mul_one]
  set t : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K :=
    ⟨spT y c, spT y (-c), by rw [spT_mul, add_neg_cancel, spT_zero],
      by rw [spT_mul, neg_add_cancel, spT_zero]⟩ with ht
  have htSp : t ∈ StatedSp 2 K := Subgroup.subset_closure (spT_symp y c)
  refine ⟨⟨t, htSp⟩, ?_⟩
  have hmv : ∀ a : K, φ (spT y a *ᵥ u₀) = a * d := by
    intro a
    rw [spT_mulVec, map_add, map_smul, hφu, zero_add, smul_eq_mul, hd']
    ring
  have hpt : pairTrace φ u₀ (⟨t, htSp⟩ : ↥(StatedSp 2 K)) = ω ^ 2 := by
    show φ (spT y c *ᵥ u₀) * φ (spT y (-c) *ᵥ u₀) = ω ^ 2
    rw [hmv, hmv]
    linear_combination (-(c * d + ω)) * hcd - ω ^ 2 * h2
  rw [hpt]
  exact sq_root_omega hω

end Sp4

section Row

variable {V : Type} [CommGroup V] [Finite V]

theorem factLieSp4FourRow1321_holds : A5.FactLieSp4FourRow1321 := by
  intro V _ _ hV2 G L v hB4 hc h
  obtain ⟨K, _, _, hK, hr⟩ := h
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  exact false_of_nat_four hV2 hB4 hc (ι := Fin 2 ⊕ Fin 2) (by simp) hK4 hr
    (fun u₀ φ hu hφ hφu => exists_pairTrace_sp4 hK4 u₀ φ hu hφ hφu)

end Row

end CFSG.Quasithin.H13.KGLie
