module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Semisimple
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Sol

public section

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type u} [Group Γ] [Finite Γ]

theorem kOf_le_khat_of_sol_eq_bot {X : Subgroup Γ} (h : sol X = ⊥) : kOf X ≤ khat X := by
  by_cases hX : Group.IsSolvable X
  · rw [khat_eq_of_isSolvable hX]
    exact kOf_le X
  · refine le_inf (kOf_le X) (le_iInf₂ fun M hM => ?_)
    have hMl : M ∈ lcal X := by
      rcases hM with ⟨hs, -⟩ | ⟨-, hmc⟩
      · exact absurd hs hX
      · rwa [← mcal_eq_lcal_of_sol_eq_bot h]
    have hK := isDirectProduct_lcal_kOf h
    rw [← hK.sSup_eq]
    refine sSup_le fun J hJ x hx => ?_
    by_cases hJM : J = M
    · subst hJM
      exact Subgroup.le_normalizer hx
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      have hcomm : ∀ m ∈ M, ∀ z ∈ J, z * m * z⁻¹ = m := fun m hm z hz => by
        have h1 := (hK.commute J hJ M hMl hJM z hz m hm).eq
        rw [h1, mul_assoc, mul_inv_cancel, mul_one]
      refine ⟨fun hy => by rwa [hcomm y hy x hx], fun hy => ?_⟩
      have h2 := hcomm _ hy x⁻¹ (inv_mem hx)
      have h3 : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
      rw [h3] at h2
      rw [h2]
      exact hy

theorem kOf_le_khat (X : Subgroup Γ) : kOf X ≤ khat X := by
  rw [SolQuot.kOf_eq_qpre_sol X, SolQuot.khat_eq_qpre_sol X]
  exact SolQuot.qpre_mono (kOf_le_khat_of_sol_eq_bot (SolQuot.sol_qimg_sol X))

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
