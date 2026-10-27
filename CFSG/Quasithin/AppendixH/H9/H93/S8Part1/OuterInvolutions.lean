module

public import CFSG.Quasithin.AppendixH.H9.H93.PsiSign
public import CFSG.Quasithin.AppendixH.H9.H93.S8Part1.OddInvolutions

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem psiExt_sq_eq_one (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) {t : MulAut (PairN 4)}
    (ht : t ∈ Mg 4) (h2 : orderOf t = 2) : psiExt ψ t ^ 2 = 1 := by
  have h := pow_orderOf_eq_one (psiExt ψ t)
  rwa [orderOf_psiExt ψ ht, h2] at h

theorem sign_psiExt_eq_neg_one (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) {t : MulAut (PairN 4)}
    (ht : t ∈ Mg 4) (hL : t ∉ Lg 4) : Equiv.Perm.sign (psiExt ψ t) = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign (psiExt ψ t)) with h | h
  · exact absurd ((mem_Lg_iff_sign ψ ht).2 h) hL
  · exact h

theorem cycleType_psiExt_of_outer_involution (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    {t : MulAut (PairN 4)} (ht : t ∈ Mg 4) (hL : t ∉ Lg 4) (h2 : orderOf t = 2) :
    (psiExt ψ t).cycleType = {2} ∨ (psiExt ψ t).cycleType = {2, 2, 2} :=
  cycleType_eq_two_or_two_two_two (psiExt_sq_eq_one ψ ht h2) (sign_psiExt_eq_neg_one ψ ht hL)

theorem exists_outer_involution (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    {σ : Equiv.Perm (Fin 8)} (h2 : orderOf σ = 2) (hs : Equiv.Perm.sign σ = -1) :
    ∃ t ∈ Mg 4, t ∉ Lg 4 ∧ orderOf t = 2 ∧ psiExt ψ t = σ := by
  refine ⟨(ψ.symm σ : MulAut (PairN 4)), (ψ.symm σ).2, ?_, ?_, ?_⟩
  · intro hL
    have h := (mem_Lg_iff_sign ψ (ψ.symm σ).2).1 hL
    rw [psiExt_coe, MulEquiv.apply_symm_apply, hs] at h
    exact absurd h (by decide)
  · rw [← orderOf_psiExt ψ (ψ.symm σ).2, psiExt_coe, MulEquiv.apply_symm_apply, h2]
  · rw [psiExt_coe, MulEquiv.apply_symm_apply]

theorem isConjIn_Mg_of_cycleType_eq (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    {t u : MulAut (PairN 4)} (ht : t ∈ Mg 4) (hu : u ∈ Mg 4)
    (h : (psiExt ψ t).cycleType = (psiExt ψ u).cycleType) : IsConjIn (Mg 4) t u := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (Equiv.Perm.isConj_iff_cycleType_eq.2 h)
  refine ⟨(ψ.symm c : MulAut (PairN 4)), (ψ.symm c).2, ?_⟩
  have hmem : ψ.symm c * (⟨t, ht⟩ : ↥(Mg 4)) * (ψ.symm c)⁻¹ = ⟨u, hu⟩ := by
    apply ψ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [psiExt_of_mem ψ ht, psiExt_of_mem ψ hu] at hc
    exact hc
  exact congrArg Subtype.val hmem

end CFSG.ASVolI.ChH
