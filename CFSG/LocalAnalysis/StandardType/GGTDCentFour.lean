module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdCent

public section

namespace CFSG.StandardType.TypeANbrDvd

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.Assembly TypeA

variable {K : Type} [Field K] [CharP K 2]

theorem isDiag_of_mul_diagonal_pairVec_four {s : Matrix (Fin 4) (Fin 4) K} (hs : s.det ≠ 0)
    {ζ : K} (hζ : ζ ≠ ζ⁻¹)
    (h : ∀ k l : Fin 4, k ≠ l → ∃ c : K,
      s * diagonal (ggPairVec k l ζ) = c • (diagonal (ggPairVec k l ζ) * s)) :
    s.IsDiag := by
  have hζ0 : ζ ≠ 0 := fun h0 => hζ (by rw [h0, _root_.inv_zero])
  intro a b hab
  obtain ⟨c, hc⟩ := h a b hab
  have hD : (diagonal (ggPairVec a b ζ)).det = 1 := by
    rw [det_diagonal, prod_ggPairVec ζ hζ0]
  have hc4 : c ^ 4 = 1 := by
    have h1 := congrArg Matrix.det hc
    rw [det_mul, det_smul, det_mul, hD, Fintype.card_fin, mul_one, one_mul] at h1
    have h2 : (c ^ 4 - 1) * s.det = 0 := by linear_combination -h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linear_combination h3
    · exact absurd h3 hs
  have hc1 : c = 1 := by
    have h2 : (c - 1) ^ 4 = 0 := by
      linear_combination hc4 + (-2 * c ^ 3 + 3 * c ^ 2 - 2 * c + 1) *
        (CharTwo.two_eq_zero : (2 : K) = 0)
    exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp h2)
  rw [hc1, one_smul] at hc
  have h1 := congrFun (congrFun hc a) b
  rw [mul_diagonal, diagonal_mul] at h1
  have hva : ggPairVec a b ζ a = ζ := by
    rw [ggPairVec_apply, if_pos rfl, if_neg hab, mul_one]
  have hvb : ggPairVec a b ζ b = ζ⁻¹ := by
    rw [ggPairVec_apply, if_neg (Ne.symm hab), if_pos rfl, one_mul]
  rw [hva, hvb] at h1
  have h2 : s a b * (ζ⁻¹ - ζ) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.mp h3).symm hζ

theorem isDiag_of_mul_diagonal_pairVec_of_four_le {d : ℕ} {s : Matrix (Fin d) (Fin d) K}
    (hs : s.det ≠ 0) (hd : 4 ≤ d) {ζ : K} (hζ : ζ ≠ ζ⁻¹)
    (h : ∀ k l : Fin d, k ≠ l → ∃ c : K,
      s * diagonal (ggPairVec k l ζ) = c • (diagonal (ggPairVec k l ζ) * s)) :
    s.IsDiag := by
  rcases Nat.lt_or_ge d 5 with h5 | h5
  · obtain rfl : d = 4 := by omega
    exact isDiag_of_mul_diagonal_pairVec_four hs hζ h
  · exact isDiag_of_mul_diagonal_pairVec hs h5 hζ h

variable {L' : Type} [Group L'] {φ' : SpecialLinearGroup (Fin 4) K →* L'}

theorem isDiag_of_conj_comm_four [Finite K] (hφker : ∀ g, φ' g = 1 → g ∈ scalars 4 K)
    {ζ : K} (hζ : ζ ≠ ζ⁻¹) {s : SpecialLinearGroup (Fin 4) K}
    (h : ∀ k l : Fin 4, k ≠ l → ∀ D : SpecialLinearGroup (Fin 4) K,
      (D : Matrix (Fin 4) (Fin 4) K) = diagonal (ggPairVec k l ζ) →
      MulAut.conj (φ' s) * MulAut.conj (φ' D) = MulAut.conj (φ' D) * MulAut.conj (φ' s)) :
    (s : Matrix (Fin 4) (Fin 4) K).IsDiag := by
  have hζ0 : ζ ≠ 0 := fun h0 => hζ (by rw [h0, _root_.inv_zero])
  refine isDiag_of_mul_diagonal_pairVec_four (by rw [s.2]; exact one_ne_zero) hζ
    fun k l hkl => ?_
  set D : SpecialLinearGroup (Fin 4) K :=
    ⟨diagonal (ggPairVec k l ζ), by rw [det_diagonal, prod_ggPairVec ζ hζ0]⟩ with hD
  have hDm : (D : Matrix (Fin 4) (Fin 4) K) = diagonal (ggPairVec k l ζ) := rfl
  have h1 : MulAut.conj (φ' s * φ' D) = MulAut.conj (φ' D * φ' s) := by
    rw [map_mul, map_mul, h k l hkl D hDm]
  set g : SpecialLinearGroup (Fin 4) K := (D * s)⁻¹ * (s * D) with hg
  have hgφ : φ' g = (φ' D * φ' s)⁻¹ * (φ' s * φ' D) := by
    rw [hg, map_mul, map_inv, map_mul, map_mul]
  have hgy : ∀ y, φ' (g * y * g⁻¹) = φ' y := by
    intro y
    have h3 : (φ' s * φ' D) * φ' y * (φ' s * φ' D)⁻¹ =
        (φ' D * φ' s) * φ' y * (φ' D * φ' s)⁻¹ := by
      have := congrArg (fun f : MulAut L' => f (φ' y)) h1
      simpa only [MulAut.conj_apply] using this
    rw [map_mul, map_mul, map_inv, hgφ]
    calc (φ' D * φ' s)⁻¹ * (φ' s * φ' D) * φ' y * ((φ' D * φ' s)⁻¹ * (φ' s * φ' D))⁻¹
        = (φ' D * φ' s)⁻¹ * ((φ' s * φ' D) * φ' y * (φ' s * φ' D)⁻¹) * (φ' D * φ' s) := by
          group
      _ = (φ' D * φ' s)⁻¹ * ((φ' D * φ' s) * φ' y * (φ' D * φ' s)⁻¹) * (φ' D * φ' s) := by
          rw [h3]
      _ = φ' y := by group
  obtain ⟨c, hc⟩ := exists_scalar_of_map_conj_eq hφker hgy
  refine ⟨c, ?_⟩
  have h4 : s * D = D * s * g := by rw [hg]; group
  have h5 := congrArg (fun x : SpecialLinearGroup (Fin 4) K => (x : Matrix (Fin 4) (Fin 4) K)) h4
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h5
  rw [hDm] at h5
  rw [h5, hc, scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

end CFSG.StandardType.TypeANbrDvd

end
