module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515f.Decomp

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.CentralizerK
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515f

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515g

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem le_outsideOrbit_of_le_centralizer_fitting_smear {B G J S : Subgroup Γ}
    (hBG : B ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcal G)
    (hSU : S ≤ kOf G ⊓ Subgroup.centralizer (B : Set Γ))
    (hs : IsSimpleGroup ↥(CFSG.inSubgroup CFSG.generalizedFitting (smear J B)))
    (hnc : ¬ IsMulCommutative ↥(CFSG.inSubgroup CFSG.generalizedFitting (smear J B)))
    (hSc : S ≤ Subgroup.centralizer
      ((CFSG.inSubgroup CFSG.generalizedFitting (smear J B) : Subgroup Γ) : Set Γ)) :
    S ≤ outsideOrbit G B J := by
  have hdp := isDirectPair_orbitClosure_outsideOrbit hBG hsol hJ
  intro s hsS
  have hsK : s ∈ kOf G := (Subgroup.mem_inf.mp (hSU hsS)).1
  set l : orbitClosure J B := pairProj hdp ⟨s, hsK⟩ with hl
  have hlT : (l : Γ) ∈ smear J B := pairProj_mem_smear hBG hsol hJ (hSU hsS)
  have hlc : ∀ f ∈ CFSG.inSubgroup CFSG.generalizedFitting (smear J B),
      f * (l : Γ) = (l : Γ) * f := by
    intro f hf
    have hfL : f ∈ orbitClosure J B :=
      smear_le_orbitClosure J B (Subgroup.map_subtype_le _ hf)
    have hfK : f ∈ kOf G := hdp.sup_eq ▸ Subgroup.mem_sup_left hfL
    have hc : (⟨f, hfK⟩ : kOf G) * ⟨s, hsK⟩ = ⟨s, hsK⟩ * ⟨f, hfK⟩ :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp (hSc hsS) f hf)
    have h1 := congrArg (pairProj hdp) hc
    rw [map_mul, map_mul] at h1
    have h2 : pairProj hdp ⟨f, hfK⟩ = ⟨f, hfL⟩ := Subtype.ext (pairProj_of_mem_left hdp hfL hfK)
    rw [h2] at h1
    exact congrArg Subtype.val h1
  have hlF : (l : Γ) ∈ CFSG.inSubgroup CFSG.generalizedFitting (smear J B) :=
    inf_centralizer_generalizedFitting_le (smear J B)
      (Subgroup.mem_inf.mpr ⟨hlT, Subgroup.mem_centralizer_iff.mpr hlc⟩)
  have hl1 : (l : Γ) = 1 := eq_one_of_forall_commute hnc hlF hlc
  obtain ⟨m, hm, hsm⟩ := pairProj_spec hdp ⟨s, hsK⟩
  have hsm' : (l : Γ) * m = s := hsm
  rw [hl1, one_mul] at hsm'
  rw [← hsm']
  exact hm

theorem eq_bot_of_le_centralizer_fitting_smear {B G S : Subgroup Γ}
    (hBG : B ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥)
    (hSU : S ≤ kOf G ⊓ Subgroup.centralizer (B : Set Γ))
    (hfit : ∀ J ∈ lcal G,
      IsSimpleGroup ↥(CFSG.inSubgroup CFSG.generalizedFitting (smear J B)) ∧
        ¬ IsMulCommutative ↥(CFSG.inSubgroup CFSG.generalizedFitting (smear J B)))
    (hSc : ∀ J ∈ lcal G, S ≤ Subgroup.centralizer
      ((CFSG.inSubgroup CFSG.generalizedFitting (smear J B) : Subgroup Γ) : Set Γ)) :
    S = ⊥ :=
  eq_bot_of_forall_le_outsideOrbit hsol (hSU.trans inf_le_left) fun J hJ =>
    le_outsideOrbit_of_le_centralizer_fitting_smear hBG hsol hJ hSU (hfit J hJ).1 (hfit J hJ).2
      (hSc J hJ)

theorem sol_inf_centralizer_eq_bot
    {p : ℕ} {A G B : Subgroup Γ} (h : KSetting p A G)
    (hKA : kDown G A = ⊥) (hBA : B ≤ A) :
    sol (G ⊓ Subgroup.centralizer (B : Set Γ)) = ⊥ := by
  have hsol : sol G = ⊥ := sol_eq_bot_of_kDown_eq_bot hKA
  have hBG : B ≤ Subgroup.normalizer (G : Set Γ) := hBA.trans h.normalizes
  refine eq_bot_of_le_centralizer_fitting_smear hBG hsol
    ((sol_le_kOf _).trans (kOf_inf_centralizer_le_kOf h hKA hBA))
    (fun J hJ => fitting_smear_isSimple h hKA hBA hJ) fun J hJ => ?_
  have hF : CFSG.inSubgroup CFSG.generalizedFitting (smear J B) ∈
      lcal (G ⊓ Subgroup.centralizer (B : Set Γ)) := by
    rw [lcal_inf_centralizer_eq h hKA hBA]
    exact ⟨J, hJ, rfl⟩
  rcases le_or_le_centralizer_of_mem_lcal hF (sol_le _) (normal_sol_subgroupOf _) with h1 | h2
  · exfalso
    obtain ⟨hs, hnc⟩ := fitting_smear_isSimple h hKA hBA hJ
    have hsolv : Group.IsSolvable ↥(CFSG.inSubgroup CFSG.generalizedFitting (smear J B)) :=
      isSolvable_of_le h1 (isSolvable_sol _)
    exact hnc (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv))
  · exact Subgroup.le_centralizer_iff.mp h2

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515g
