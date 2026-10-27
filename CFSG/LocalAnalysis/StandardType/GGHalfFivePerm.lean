module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveCommutant

public section

namespace CFSG.StandardType.GGHalf

open CFSG.StandardType CFSG.LieType.Universal.SpecialLinear Matrix

private theorem f4_two_eq_zero : (2 : F4) = 0 := CharTwo.two_eq_zero

private theorem sigmaPerm_finProdFinEquiv (i : Fin 3) (j : Fin 2) :
    sigmaPerm 3 (finProdFinEquiv (i, j)) = finProdFinEquiv (Equiv.swap 0 1 i, j) := by
  fin_cases i <;> fin_cases j <;>
    simp [sigmaPerm, finProdFinEquiv, Equiv.swap_apply_def]

private theorem tauPerm_finProdFinEquiv (i : Fin 3) (j : Fin 2) :
    tauPerm 3 (finProdFinEquiv (i, j)) = finProdFinEquiv (Equiv.swap 0 2 i, j) := by
  fin_cases i <;> fin_cases j <;>
    simp [tauPerm, finProdFinEquiv, Equiv.swap_apply_def]

private theorem slPerm_sigma_eq :
    slPerm gf2_two (sigmaPerm 3) =
      resSL 3 (slPerm f4_two_eq_zero (Equiv.swap 0 1 : Equiv.Perm (Fin 3))) := by
  apply Subtype.ext
  ext r s
  obtain ⟨⟨i, j⟩, rfl⟩ := (finProdFinEquiv (m := 3) (n := 2)).surjective r
  obtain ⟨⟨i', j'⟩, rfl⟩ := (finProdFinEquiv (m := 3) (n := 2)).surjective s
  rw [coe_slPerm, coe_resSL, resMat_apply, coe_slPerm, signedPerm_apply,
    sigmaPerm_finProdFinEquiv]
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [signedPerm_apply, finProdFinEquiv, Equiv.swap_apply_def]

private theorem slPerm_tau_eq :
    slPerm gf2_two (tauPerm 3) =
      resSL 3 (slPerm f4_two_eq_zero (Equiv.swap 0 2 : Equiv.Perm (Fin 3))) := by
  apply Subtype.ext
  ext r s
  obtain ⟨⟨i, j⟩, rfl⟩ := (finProdFinEquiv (m := 3) (n := 2)).surjective r
  obtain ⟨⟨i', j'⟩, rfl⟩ := (finProdFinEquiv (m := 3) (n := 2)).surjective s
  rw [coe_slPerm, coe_resSL, resMat_apply, coe_slPerm, signedPerm_apply,
    tauPerm_finProdFinEquiv]
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [signedPerm_apply, finProdFinEquiv, Equiv.swap_apply_def]

theorem slPerm_sigma_mem_sl3four : slPerm gf2_two (sigmaPerm 3) ∈ sl3four := by
  change slPerm gf2_two (sigmaPerm 3) ∈ (resSL 3).range
  rw [MonoidHom.mem_range]
  exact ⟨_, slPerm_sigma_eq.symm⟩

theorem slPerm_tau_mem_sl3four : slPerm gf2_two (tauPerm 3) ∈ sl3four := by
  change slPerm gf2_two (tauPerm 3) ∈ (resSL 3).range
  rw [MonoidHom.mem_range]
  exact ⟨_, slPerm_tau_eq.symm⟩

end CFSG.StandardType.GGHalf

end
