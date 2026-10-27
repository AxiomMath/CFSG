module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515.Core
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Sol

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515ab

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem le_kDown_of_sol_eq_bot
    {p : ℕ} {A G X : Subgroup Γ} (h : KSetting p A G)
    (hX : IsDAInvariant A G X) (hsol : sol G = ⊥)
    (hsolv : Group.IsSolvable (X ⊓ Subgroup.centralizer (A : Set Γ) : Subgroup Γ)) :
    X ≤ kDown G A := by
  have hcent : ∀ J ∈ lcalA G A, X ≤ Subgroup.centralizer (J : Set Γ) := by
    intro J hJ
    rcases lemma_5_14 h hX hsol hJ with hF | hC
    · exfalso
      obtain ⟨hs, hnc⟩ := smear_fitting_isSimple h hJ
      have hle : CFSG.inSubgroup CFSG.generalizedFitting (smear J A) ≤
          X ⊓ Subgroup.centralizer (A : Set Γ) :=
        le_inf hF ((Subgroup.map_subtype_le _).trans (smear_le_centralizer J A))
      exact not_isSolvable_of_not_isMulCommutative hnc (isSolvable_of_le hle hsolv)
    · exact hC
  intro x hx
  refine mem_kDown_iff.mpr ⟨hX.1 hx, fun k hk => ?_⟩
  have hk' : k ∈ Subgroup.centralizer ({x} : Set Γ) := by
    refine (iSup₂_le (fun M hM => ?_) : kUp G A ≤ Subgroup.centralizer ({x} : Set Γ)) hk
    have hM' : M ∈ lcalA G A := ⟨(mcal_eq_lcal_of_sol_eq_bot hsol) ▸ hM.1, hM.2⟩
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hcent M hM' hx) y hy
  rw [hsol, Subgroup.mem_bot]
  rw [Subgroup.mem_centralizer_singleton_iff] at hk'
  exact commutatorElement_eq_one_iff_mul_comm.mpr hk'.symm

theorem le_kDown_of_isSolvable_inf_centralizer
    {p : ℕ} {A G X : Subgroup Γ} (h : KSetting p A G)
    (hX : IsDAInvariant A G X)
    (hsolv : Group.IsSolvable (X ⊓ Subgroup.centralizer (A : Set Γ) : Subgroup Γ)) :
    X ≤ kDown G A := by
  refine SolQuot.le_kDown_of_qimg_le_sol h hX.1 ?_
  exact le_kDown_of_sol_eq_bot (SolQuot.kSetting_qimg_sol h)
    (SolQuot.isDAInvariant_qimg_sol h hX) (SolQuot.sol_qimg_sol G)
    (((SolQuot.qSetting_sol h).isSolvable_qimg_inf_centralizer_iff hX.1 hX.2.2).mpr hsolv)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515ab
