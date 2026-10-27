module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTvRank

public section

namespace CFSG.StandardType.LinTwoTv

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem eq_zero_or_eq_one_of_card_two (hK : Nat.card K = 2) (x : K) : x = 0 ∨ x = 1 := by
  have := Fintype.ofFinite K
  rcases eq_or_ne x 0 with h | h
  · exact .inl h
  · right
    have h1 := FiniteField.pow_card_sub_one_eq_one x h
    rwa [← Nat.card_eq_fintype_card, hK, show 2 - 1 = 1 from rfl, pow_one] at h1

theorem ringEquiv_eq_one (hK : Nat.card K = 2) (σ : K ≃+* K) : σ = 1 := by
  ext x
  rcases eq_zero_or_eq_one_of_card_two hK x with h | h
  · rw [h]
    simp
  · rw [h]
    simp

theorem exists_rank_pres_hom (hK : Nat.card K = 2) (hd : 3 ≤ d)
    (φ : MulAut (projectiveSL d K)) :
    ∃ Θ : GL (Fin d) K →* GL (Fin d) K, (∀ B, wtGL (Θ B) = wtGL B) ∧
      ∀ B, φ * conjAut d K B * φ⁻¹ = conjAut d K (Θ B) := by
  obtain ⟨M, σ, ε, hε, hφ⟩ := (automorphism_generation (K := K) hd).2 φ
  have hσ : σ = 1 := ringEquiv_eq_one hK σ
  have htrans := standard_automorphism_transport (K := K) (n := d)
  have hδ : (dualAut d K)⁻¹ = dualAut d K := inv_eq_of_mul_eq_one_right htrans.2.2.2.1
  rw [hσ, map_one, mul_one] at hφ
  subst hφ
  interval_cases ε
  · refine ⟨(MulAut.conj M).toMonoidHom, fun B => wtGL_conj M B, fun B => ?_⟩
    rw [pow_zero, mul_one, ← map_inv, ← map_mul, ← map_mul]
    rfl
  · refine ⟨(MulAut.conj M).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.inverseTranspose : GL (Fin d) K ≃* GL (Fin d) K).toMonoidHom,
      fun B => ?_, fun B => ?_⟩
    · exact (wtGL_conj M _).trans (wtGL_inverseTranspose B)
    · have h1 := htrans.2.2.2.2.1 B
      rw [pow_one, _root_.mul_inv_rev, hδ]
      calc conjAut d K M * dualAut d K * conjAut d K B * (dualAut d K * (conjAut d K M)⁻¹)
          = conjAut d K M * (dualAut d K * conjAut d K B * dualAut d K) *
              (conjAut d K M)⁻¹ := by group
        _ = conjAut d K (M * Matrix.GeneralLinearGroup.inverseTranspose B * M⁻¹) := by
          rw [h1, map_mul, map_mul, map_inv]
        _ = _ := rfl

end CFSG.StandardType.LinTwoTv

end
