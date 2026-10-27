module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.CentralizerK.Basic

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.CentralizerK

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem isSolvable_inf_centralizer_kOf {p : ℕ} {A G : Subgroup Γ} (h : KSetting p A G)
    (hM : mcalA G A = ∅) :
    Group.IsSolvable (kOf G ⊓ Subgroup.centralizer (A : Set Γ) : Subgroup Γ) := by
  have hq := SolQuot.qSetting_sol h
  have hsol := SolQuot.sol_qimg_sol G
  have hMbar : mcalA (AChief.qimg (sol G) G) (AChief.qimg (sol G) A) = ∅ := by
    rw [← (SolQuot.bijOn_mcalA hq).image_eq, hM, Set.image_empty]
  have hS : ∀ J ∈ lcal (AChief.qimg (sol G) G),
      Group.IsSolvable ↥(smear J (AChief.qimg (sol G) A)) := by
    intro J hJ
    by_contra hns
    have hmem : J ∈ mcalA (AChief.qimg (sol G) G) (AChief.qimg (sol G) A) :=
      ⟨(mcal_eq_lcal_of_sol_eq_bot hsol).symm ▸ hJ, hns⟩
    rw [hMbar] at hmem
    exact hmem
  have hbar := isSolvable_inf_centralizer_kOf_of_sol_eq_bot
    (SolQuot.kSetting_qimg_sol h).normalizes hsol hS
  rw [SolQuot.kOf_qimg_sol le_rfl] at hbar
  exact (hq.isSolvable_qimg_inf_centralizer_iff (kOf_le G)
    (le_normalizer_kOf_of_le_normalizer h.normalizes)).mp hbar

theorem lcalA_eq_lcal_of_kDown_eq_bot
    {p : ℕ} {A G : Subgroup Γ} (h : KSetting p A G)
    (hKA : kDown G A = ⊥) : lcalA G A = lcal G := by
  have hsol : sol G = ⊥ := sol_eq_bot_of_kDown_eq_bot hKA
  refine Set.Subset.antisymm (lcalA_subset G A) fun J hJ => ?_
  by_contra hJA
  have hJS : J ∈ lcal G \ lcalA G A := ⟨hJ, hJA⟩
  have hdp : IsDirectProduct (lcal G \ lcalA G A) (sSup (lcal G \ lcalA G A)) :=
    isDirectProduct_of_subset (isDirectProduct_lcal_kOf hsol) Set.sdiff_subset
  have hsolv := isSolvable_inf_centralizer_of_isDirectProduct hdp
    (fun a ha _ hJ' => map_conj_mem_lcal_diff_lcalA hJ' (h.normalizes ha) (Or.inl ha))
    (fun J' hJ' => (isSolvable_inf_centralizer_iff_smear h.normalizes hJ'.1).mpr (by
      by_contra hns
      exact hJ'.2 ⟨hJ'.1, hns⟩))
  have hY := theorem_5_15_a h (isDAInvariant_sSup_lcal_diff_lcalA h.normalizes) hsolv
  rw [hKA] at hY
  exact ne_bot_of_not_isMulCommutative (mem_lcal_iff.mp hJ).2.2.2
    (le_bot_iff.mp ((le_sSup hJS).trans hY))

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
