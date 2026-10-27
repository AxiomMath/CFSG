module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAk
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Aset
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R35
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R36
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThreeOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem c33_gammaSet_le_centralizer (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D)
    (hext : DataExt D) (h5 : R16_5 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {m : ℕ} (hm : Case1633 D V₀ V hV L m) {i : ℕ} (hi : i + 1 ≤ m)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V i D.M) : A ≤ centralizer (V : Set G) := by
  classical
  obtain ⟨S, hSω, hSK⟩ := exists_omegaModel_of_case1633 hm
  obtain ⟨hδ, hr⟩ := r16_35_holds D h61 hext h5 V₀ V L hV hS m hm
  have h := hS.setting.hyp16
  have hP := h.hyp125.pairFacts
  have hempty := S.aSet_succ_eq_empty hSK (Mbar_le_normalizer_lBar hS S hSω)
  have hAM : A ∈ E3.gammaSet V i D.M := hA
  obtain ⟨hAMle, g, hAg, -⟩ := hA
  have hbar : barSub V₀ V hV A = ⊥ := by
    by_contra hne
    have hrk : (((m + 1) + i + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V :=
      le_trans (by exact_mod_cast (by omega : (m + 1) + i + mSub V₀ ≤ 2 * m + mSub V₀)) hr
    have hδ' : (((m + 1) + i : ℕ) : ℕ∞) ≤ deltaInf D.M V :=
      le_trans (by exact_mod_cast (by omega : (m + 1) + i ≤ 2 * m)) hδ
    have hmem := barSub_mem_calABar_of_gammaSet D hSg h1219 h21 h22 h hrk hδ' hAM hne
    exact (Set.eq_empty_iff_forall_notMem.1 hempty) _ hmem
  have hi0 : ((i + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : i + mSub V₀ < 2 * m + mSub V₀)) hr
  obtain ⟨-, hc, -⟩ := sixteen_twentyThree_one D h22 h hAM hAg hi0
  have hCt := (WeakClosure81.barSub_eq_bot_iff hV hP.le_normalizer hP.le_normalizer₀
    hAMle).1 hbar
  have hVc : V ≤ centralizer (A : Set G) := fun v hv => hc v hv fun a ha => by
    have hcm := WeakClosure81.centralizesMod_of_mem_cTilde hV hP.le_normalizer
      hP.le_normalizer₀ (hCt ha) v hv
    have e : ⁅v, a⁆ = (a * v * a⁻¹ * v⁻¹)⁻¹ := by group
    rw [e]
    exact V₀.inv_mem hcm
  exact Subgroup.le_centralizer_iff.1 hVc

theorem autI_top_eq_of_normalizer_eq {V M : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : Subgroup.normalizer (V : Set G) = M) : autI hV (⊤ : Subgroup G) = autI hV M := by
  refine le_antisymm (fun φ hφ => ?_) (autI_mono hV le_top)
  obtain ⟨g, -, rfl⟩ := (mem_autI hV).1 hφ
  exact (mem_autI hV).2 ⟨g, by rw [← hM]; exact g.2, rfl⟩

theorem c33_aSet_two_of_case1633 (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D)
    (hext : DataExt D) (h5 : R16_5 D) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D ⊥ V L hV) (hm : Case1633 D ⊥ V hV L 2) {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V 2 D.M) (hnc : ¬ A ≤ centralizer (V : Set G)) :
    autI hV A ∈ E3.aSet 2 (autI hV ⊤) := by
  classical
  obtain ⟨hδ, hr⟩ := r16_35_holds D h61 hext h5 ⊥ V L hV hS 2 hm
  have h := hS.setting.hyp16
  have hMN : Subgroup.normalizer (V : Set G) = D.M := h.hyp125.normalizer_eq
  have hA1 : barSub ⊥ V hV A ≠ ⊥ := by
    intro h0
    rw [TwelveTwentyThree.barSub_bot_eq_map_autI,
      Subgroup.map_eq_bot_iff_of_injective _ (MulAut.congr _).injective,
      autI_eq_bot_iff hV (hMN ▸ hA.1)] at h0
    exact hnc h0
  have hrk : (((2 + 2 + mSub (⊥ : Subgroup G) : ℕ)) : ℕ∞) ≤ rMV D.M V := by
    have : (2 + 2 + mSub (⊥ : Subgroup G) : ℕ) = 2 * 2 + mSub (⊥ : Subgroup G) := by omega
    rw [this]; exact hr
  have hδ' : (((2 + 2 : ℕ)) : ℕ∞) ≤ deltaInf D.M V := by
    have : (2 + 2 : ℕ) = 2 * 2 := by norm_num
    rw [this]; exact hδ
  have hmem := barSub_mem_calABar_of_gammaSet D hSg h1219 h21 h22 h (i := 2) (k := 2) hrk hδ' hA
    hA1
  unfold calABar at hmem
  change barSub ⊥ V hV A ∈ E3.aSet 2 (barSub ⊥ V hV D.M) at hmem
  rw [TwelveTwentyThree.barSub_bot_eq_map_autI, TwelveTwentyThree.barSub_bot_eq_map_autI] at hmem
  rw [autI_top_eq_of_normalizer_eq hV hMN]
  exact (aSet_map_congr_equiv_iff (TwelveShort.mkTilEquiv V hV) 2 _ _).1 hmem

theorem omega_ofEquiv_map {W W' : Type} [CommGroup W] [CommGroup W'] (S : OmegaModel W)
    (φ : W' ≃* W) : (S.ofEquiv φ).omega.map (MulAut.congr φ).toMonoidHom = S.omega := by
  rw [S.omega_ofEquiv, Subgroup.map_map]
  have h : (MulAut.congr φ).toMonoidHom.comp (MulAut.congr φ.symm).toMonoidHom =
      MonoidHom.id _ := MonoidHom.ext fun x => MulEquiv.ext fun v => by simp
  rw [h, Subgroup.map_id]

theorem c33_orth_of_case1633 (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D ⊥ V L hV) (hm : Case1633 D ⊥ V hV L 2) : C33Orth V hV := by
  classical
  obtain ⟨S, hSω, hSK⟩ := exists_omegaModel_of_case1633 hm
  have hMb := Mbar_le_normalizer_lBar hS S hSω
  have hMN : Subgroup.normalizer (V : Set G) = D.M := hS.setting.hyp16.hyp125.normalizer_eq
  set φ := TwelveShort.mkTilEquiv V hV with hφ
  refine ⟨S.ofEquiv φ, by rw [OmegaModel.ofEquiv_card_K, hSK]; norm_num, ?_⟩
  have h2 : (autI hV D.M).map (MulAut.congr φ).toMonoidHom ≤
      Subgroup.normalizer (((S.ofEquiv φ).omega.map (MulAut.congr φ).toMonoidHom : Subgroup _) :
        Set _) := by
    rw [← TwelveTwentyThree.barSub_bot_eq_map_autI, omega_ofEquiv_map]
    exact hMb
  rw [autI_top_eq_of_normalizer_eq hV hMN]
  exact (map_le_normalizer_map_iff (MulAut.congr φ) _ _).1 h2

theorem c33_setting_of_case1633 (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D)
    (hext : DataExt D) (h5 : R16_5 D) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D ⊥ V L hV) (hm : Case1633 D ⊥ V hV L 2) : C33Setting D.M V where
  elemAbelian := hV
  normalizer_eq := hS.setting.hyp16.hyp125.normalizer_eq
  orth := c33_orth_of_case1633 D hS hm
  gamma_le := fun i hi A hA =>
    c33_gammaSet_le_centralizer D hSg h1219 h21 h22 h61 hext h5 hS hm (by omega) hA
  aSet_two := fun A hA hnc => c33_aSet_two_of_case1633 D hSg h1219 h21 h22 h61 hext h5 hS hm hA hnc
  lt_rMV := r16_36_holds D h61 hext h5 ⊥ V L hV hS 2 hm rfl rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
