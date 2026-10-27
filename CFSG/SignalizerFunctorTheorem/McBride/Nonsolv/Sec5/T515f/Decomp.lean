module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515cd
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515f.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515f.Orbit

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.CentralizerK

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515f

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem kUp_le_kOf {G : Subgroup Γ} (hsol : sol G = ⊥) (A : Subgroup Γ) : kUp G A ≤ kOf G := by
  refine iSup₂_le fun M hM => (isDirectProduct_lcal_kOf hsol).le ?_
  rw [← mcal_eq_lcal_of_sol_eq_bot hsol]
  exact mcalA_subset G A hM

theorem kOf_inf_centralizer_le_kOf
    {p : ℕ} {A G B : Subgroup Γ} (h : KSetting p A G)
    (hKA : kDown G A = ⊥) (hBA : B ≤ A) :
    kOf (G ⊓ Subgroup.centralizer (B : Set Γ)) ≤ kOf G ⊓ Subgroup.centralizer (B : Set Γ) := by
  have hsol : sol G = ⊥ := sol_eq_bot_of_kDown_eq_bot hKA
  have hAC : A ≤ Subgroup.centralizer (B : Set Γ) := fun a ha => by
    have := h.elemAbelian.1
    exact Subgroup.mem_centralizer_iff.mpr fun b hb =>
      congrArg Subtype.val (mul_comm' (⟨b, hBA hb⟩ : A) ⟨a, ha⟩)
  have hAV : A ≤ Subgroup.normalizer ((G ⊓ Subgroup.centralizer (B : Set Γ) : Subgroup Γ) :
      Set Γ) := fun a ha => mem_normalizer_inf (h.normalizes ha) (Subgroup.le_normalizer (hAC ha))
  have hDV : G ⊓ Subgroup.centralizer (A : Set Γ) ≤ G ⊓ Subgroup.centralizer (B : Set Γ) :=
    inf_le_inf_left G (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBA))
  have hX : IsDAInvariant A G (kOf (G ⊓ Subgroup.centralizer (B : Set Γ))) :=
    ⟨(kOf_le _).trans inf_le_left, fun _ hd => le_normalizer_kOf _ (hDV hd),
      le_normalizer_kOf_of_le_normalizer hAV⟩
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := theorem_5_15_d h hX (kOf_kOf _) x hx
  rw [hKA, Subgroup.mem_bot] at hz
  subst hz
  rw [mul_one] at hx ⊢
  exact Subgroup.mem_inf.mpr ⟨kUp_le_kOf hsol A hy, (Subgroup.mem_inf.mp (kOf_le _ hx)).2⟩

theorem kOf_inf_centralizer_eq
    {p : ℕ} {A G B : Subgroup Γ} (h : KSetting p A G)
    (hKA : kDown G A = ⊥) (hBA : B ≤ A) :
    kOf (G ⊓ Subgroup.centralizer (B : Set Γ)) =
      kOf (kOf G ⊓ Subgroup.centralizer (B : Set Γ)) :=
  (kOf_eq_of_kOf_le (kOf_inf_centralizer_le G) (kOf_inf_centralizer_le_kOf h hKA hBA)).symm

theorem lcal_inf_centralizer_eq
    {p : ℕ} {A G B : Subgroup Γ} (h : KSetting p A G)
    (hKA : kDown G A = ⊥) (hBA : B ≤ A) :
    lcal (G ⊓ Subgroup.centralizer (B : Set Γ)) =
      {Y | ∃ J ∈ lcal G, Y = CFSG.inSubgroup CFSG.generalizedFitting (smear J B)} := by
  have hsol : sol G = ⊥ := sol_eq_bot_of_kDown_eq_bot hKA
  have hBG : B ≤ Subgroup.normalizer (G : Set Γ) := hBA.trans h.normalizes
  have hkV := kOf_inf_centralizer_le_kOf h hKA hBA
  have hUV := kOf_inf_centralizer_le (B := B) G
  ext Y
  constructor
  · intro hY
    obtain ⟨-, -, hYs, hYnc⟩ := mem_lcal_iff.mp hY
    have hYU : Y ≤ kOf G ⊓ Subgroup.centralizer (B : Set Γ) :=
      (L511.le_kOf_of_mem_lcal hY).trans hkV
    have hYU' : Y ∈ lcal (kOf G ⊓ Subgroup.centralizer (B : Set Γ)) :=
      L511.mem_lcal_of_le hY hYU hUV
    obtain ⟨J, hJ, hYJ⟩ : ∃ J ∈ lcal G, ¬ Y ≤ outsideOrbit G B J := by
      by_contra hcon
      push Not at hcon
      exact ne_bot_of_not_isMulCommutative hYnc
        (eq_bot_of_forall_le_outsideOrbit hsol (hYU.trans inf_le_left) hcon)
    have hTU := smear_le_kOf_inf_centralizer hBG hsol hJ
    rcases le_or_le_centralizer_of_mem_lcal hYU' hTU (normal_smear_subgroupOf hBG hsol hJ) with
      h1 | h2
    · refine ⟨J, hJ, ?_⟩
      have := L511.mem_lcal_of_le hYU' h1 hTU
      rw [lcal_smear_eq h hKA hBA hJ] at this
      exact this
    · exact absurd (le_outsideOrbit_of_le_centralizer_smear hBG hsol hJ hYU hYs hYnc h2) hYJ
  · rintro ⟨J, hJ, rfl⟩
    obtain ⟨hs, hnc⟩ := fitting_smear_isSimple h hKA hBA hJ
    have hTU := smear_le_kOf_inf_centralizer hBG hsol hJ
    have hFT : CFSG.inSubgroup CFSG.generalizedFitting (smear J B) ≤ smear J B :=
      Subgroup.map_subtype_le _
    refine mem_lcal_iff.mpr ⟨hFT.trans (hTU.trans hUV), ?_, hs, hnc⟩
    exact isSubnormal_subgroupOf_trans (hFT.trans hTU) hUV
      (isSubnormal_subgroupOf_trans hFT hTU
        (normal_inSubgroup_generalizedFitting (smear J B)).isSubnormal
        (normal_smear_subgroupOf hBG hsol hJ).isSubnormal)
      (normal_kOf_inf_centralizer_subgroupOf G B).isSubnormal

theorem fitting_smear_eq_iff
    {p : ℕ} {A G B J J' : Subgroup Γ} (h : KSetting p A G)
    (hKA : kDown G A = ⊥) (hBA : B ≤ A) (hJ : J ∈ lcal G) (hJ' : J' ∈ lcal G) :
    CFSG.inSubgroup CFSG.generalizedFitting (smear J B) =
        CFSG.inSubgroup CFSG.generalizedFitting (smear J' B) ↔
      ∃ b ∈ B, J' = J.map (MulAut.conj b).toMonoidHom := by
  have hsol : sol G = ⊥ := sol_eq_bot_of_kDown_eq_bot hKA
  have hBG : B ≤ Subgroup.normalizer (G : Set Γ) := hBA.trans h.normalizes
  constructor
  · intro hEq
    by_contra hcon
    have hbot := inf_orbitClosure_eq_bot_of_not_mem_conjOrbit hBG hsol hJ hJ' hcon
    refine ne_bot_of_not_isMulCommutative (fitting_smear_isSimple h hKA hBA hJ).2
      (eq_bot_iff.mpr (le_trans (le_inf ?_ ?_) hbot.le))
    · exact (Subgroup.map_subtype_le _).trans (smear_le_orbitClosure J B)
    · rw [hEq]
      exact (Subgroup.map_subtype_le _).trans (smear_le_orbitClosure J' B)
  · rintro ⟨b, hb, rfl⟩
    rw [smear_map_conj_of_mem hb]

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515f
