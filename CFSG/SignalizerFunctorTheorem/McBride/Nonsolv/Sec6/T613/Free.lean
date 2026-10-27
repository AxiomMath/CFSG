module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515f.Decomp

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.CentralizerK

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T613

variable {Γ : Type*} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem orbitClosure_le_outsideOrbit {B G J J' : Subgroup Γ}
    (hBG : B ≤ Subgroup.normalizer (G : Set Γ)) (hJ' : J' ∈ lcal G) (h : J' ∉ conjOrbit B J) :
    orbitClosure J' B ≤ outsideOrbit G B J := by
  rw [orbitClosure_eq_sSup]
  refine sSup_le_sSup fun K hK => ⟨conjOrbit_subset_lcal hBG hJ' hK, fun hKJ => h ?_⟩
  obtain ⟨b, hb, rfl⟩ := hK
  have := map_conj_mem_conjOrbit hKJ (inv_mem hb)
  rwa [map_conj_map_conj_inv] at this

omit [Finite Γ] in
theorem not_mem_conjOrbit_of_ne {B J J' : Subgroup Γ} (h : orbitClosure J' B ≠ orbitClosure J B) :
    J' ∉ conjOrbit B J := by
  rintro ⟨b, hb, rfl⟩
  exact h (orbitClosure_map_conj hb)

theorem isDirectProduct_orbitClosures {B G : Subgroup Γ}
    (hBG : B ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥) :
    IsDirectProduct {O | ∃ J ∈ lcal G, O = orbitClosure J B} (kOf G) where
  commute := by
    rintro _ ⟨J₁, hJ₁, rfl⟩ _ ⟨J₂, hJ₂, rfl⟩ hne x hx y hy
    exact commute_of_mem_orbitClosure hBG hsol hJ₁ hx (orbitClosure_le_outsideOrbit hBG hJ₂
      (not_mem_conjOrbit_of_ne (Ne.symm hne)) hy)
  indep := by
    rintro _ ⟨J, hJ, rfl⟩
    have hdp := isDirectPair_orbitClosure_outsideOrbit hBG hsol hJ
    refine Disjoint.mono_right (sSup_le ?_) (disjoint_iff.mpr hdp.inf_eq_bot)
    rintro _ ⟨⟨J', hJ', rfl⟩, hne⟩
    exact orbitClosure_le_outsideOrbit hBG hJ' (not_mem_conjOrbit_of_ne hne)
  sSup_eq := by
    have hK := isDirectProduct_lcal_kOf hsol
    refine le_antisymm (sSup_le ?_) ?_
    · rintro _ ⟨J, hJ, rfl⟩
      exact orbitClosure_le_kOf hBG hsol hJ
    · rw [← hK.sSup_eq]
      exact sSup_le fun J hJ => (le_orbitClosure J B).trans (le_sSup ⟨J, hJ, rfl⟩)

theorem inf_centralizer_le_sSup_smear {B G : Subgroup Γ}
    (hBG : B ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥) :
    kOf G ⊓ Subgroup.centralizer (B : Set Γ) ≤ sSup {X | ∃ J ∈ lcal G, X = smear J B} := by
  have hS := isDirectProduct_orbitClosures hBG hsol
  have hA : ∀ a ∈ B, ∀ O ∈ {O | ∃ J ∈ lcal G, O = orbitClosure J B},
      O.map (MulAut.conj a).toMonoidHom ∈ {O | ∃ J ∈ lcal G, O = orbitClosure J B} := by
    rintro a ha _ ⟨J, hJ, rfl⟩
    exact ⟨J, hJ, Subgroup.mem_normalizer_iff_map_conj_eq.mp (mem_normalizer_orbitClosure ha)⟩
  have hset : {K | ∃ O ∈ {O | ∃ J ∈ lcal G, O = orbitClosure J B},
      K = O ⊓ Subgroup.centralizer (B : Set Γ)} = {X | ∃ J ∈ lcal G, X = smear J B} := by
    ext X
    constructor
    · rintro ⟨_, ⟨J, hJ, rfl⟩, rfl⟩
      exact ⟨J, hJ, rfl⟩
    · rintro ⟨J, hJ, rfl⟩
      exact ⟨_, ⟨J, hJ, rfl⟩, rfl⟩
  rw [← hset]
  refine (Near.Thm210.le_sSup_image_iff hS
    (T := fun O => O ⊓ Subgroup.centralizer (B : Set Γ)) fun O _ => inf_le_left).mpr
    ⟨inf_le_left, ?_⟩
  rintro _ ⟨J, hJ, rfl⟩
  have h1 := projIn_centralizer_eq hS hA (J := orbitClosure J B) ⟨J, hJ, rfl⟩
  have hBO : B ⊓ Subgroup.normalizer ((orbitClosure J B : Subgroup Γ) : Set Γ) = B :=
    inf_eq_left.mpr fun a ha => mem_normalizer_orbitClosure ha
  rw [hBO] at h1
  exact h1.le

theorem nonempty_mulEquiv_smear_of_le_centralizer {B G J : Subgroup Γ}
    (hBG : B ≤ Subgroup.normalizer (G : Set Γ)) (hJ : J ∈ lcal G)
    (hN : B ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.centralizer (J : Set Γ)) :
    Nonempty (↥(smear J B) ≃* ↥J) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_smear hBG hJ
  have h : J ⊓ Subgroup.centralizer ((B ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ) =
      J := inf_eq_left.mpr (Subgroup.le_centralizer_iff.mpr hN)
  exact ⟨e.trans (MulEquiv.subgroupCongr h)⟩

theorem kOf_inf_centralizer_le_kOf_of_free {B G : Subgroup Γ}
    (hBG : B ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥)
    (hfree : ∀ J ∈ lcal G,
      B ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.centralizer (J : Set Γ)) :
    kOf G ⊓ Subgroup.centralizer (B : Set Γ) ≤
      kOf (kOf G ⊓ Subgroup.centralizer (B : Set Γ)) := by
  refine (inf_centralizer_le_sSup_smear hBG hsol).trans (sSup_le ?_)
  rintro _ ⟨J, hJ, rfl⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_smear_of_le_centralizer hBG hJ (hfree J hJ)
  obtain ⟨-, -, hs, hnc⟩ := mem_lcal_iff.mp hJ
  exact L511.le_kOf_of_mem_lcal (mem_lcal_iff.mpr
    ⟨T515f.smear_le_kOf_inf_centralizer hBG hsol hJ,
      (T515f.normal_smear_subgroupOf hBG hsol hJ).isSubnormal, e.isSimpleGroup,
      fun hc => hnc ((isMulCommutative_congr e).mp hc)⟩)

theorem kOf_kOf_inf_centralizer_of_free {B G : Subgroup Γ}
    (hBG : B ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥)
    (hfree : ∀ J ∈ lcal G,
      B ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.centralizer (J : Set Γ)) :
    kOf (kOf G ⊓ Subgroup.centralizer (B : Set Γ)) = kOf G ⊓ Subgroup.centralizer (B : Set Γ) :=
  le_antisymm (kOf_le _) (kOf_inf_centralizer_le_kOf_of_free hBG hsol hfree)

theorem kOf_inf_centralizer_eq_kOf_of_free
    {p : ℕ} {A G B : Subgroup Γ} (h : KSetting p A G)
    (hKA : kDown G A = ⊥) (hBA : B ≤ A)
    (hfree : ∀ J ∈ lcal G,
      B ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.centralizer (J : Set Γ)) :
    kOf G ⊓ Subgroup.centralizer (B : Set Γ) = kOf (G ⊓ Subgroup.centralizer (B : Set Γ)) :=
  (kOf_kOf_inf_centralizer_of_free (hBA.trans h.normalizes) (sol_eq_bot_of_kDown_eq_bot hKA)
    hfree).symm.trans (T515f.kOf_inf_centralizer_eq h hKA hBA).symm

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T613
