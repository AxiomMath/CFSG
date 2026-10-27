module

public import CFSG.Quasithin.Vol2.Ch7Lem734Loc
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318T
public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsQ
public import CFSG.Quasithin.Vol2.Ch8Sec2D4Inputs
public import CFSG.Quasithin.Vol2.Ch8Sec2L825L

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
open scoped IsMulCommutative

section L822A

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem setting_822 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (h331 : Stmt3_3_1) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (hyp : Hyp7_0_2 G T L I) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) :
    MinParabolic H T (H ⊓ fsuM T L) ∧ SQTKGroup ↥H ∧ QuasithinUnique.CharTwo H ∧
      H ⊓ fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
  have hU := lemma_1_2_7_three hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian h37 h38 h39
    hyp.fsu.sylow hyp.fsu.maximal
  have hInM : InM T (fsuM T L) := ⟨hU.1.1, le_sup_right.trans hU.1.2⟩
  have hNT : Subgroup.normalizer (T : Set G) ≤ fsuM T L :=
    ((h331 G T hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.sylow).2 L
      hyp.fsu.maximal hyp.fsu.quasisimple).2.2.2.1
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.fsu.sylow
  have hUM : IsUniqueMaxOver H T (H ⊓ fsuM T L) := by
    have := IsHStar.isUniqueMaxOver P (hP ▸ hH) (hP ▸ hInM.2)
    rwa [hP] at this
  have hloc := inf_fsuM_eq_of_normal hC58 h317 h37 h38 h39 h3228 h325 hyp hTL hH
  refine ⟨⟨isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hH.1.1,
    hH.not_le_normalizer hNT, hUM⟩,
    sqtkGroup_of_pCoreOf_ne_bot hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian hH.1.2,
    charTwo_of_inH' hyp.fsu.qtke hyp.fsu.sylow hH.1, ?_⟩
  rw [hloc]
  exact inf_le_right

theorem not_le_pCoreOf_822 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h316 : Theorem316Statement) (hQ : HQ82) (hM22 : Step822M22)
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) (h821 : Hyp8_2_1 T L I)
    [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Case8_2 T L I)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) : ¬ fsuV T I ≤ pCoreOf 2 H := by
  by_cases hex : Row711M22Code T L I ∧ ¬ autOn T (fsuV T I) ≤ autOn (fsuL0 T L) (fsuV T I)
  · exact hM22 G T L I hyp h731 h821 hc hrow hex.1 hex.2 H hH
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have h318 := hyp318_of_normal h37 h38 h39 h3228 hyp hTL hH
  have hover : Mathieu.IsOver (autI hV (fsuL0 T L)) (autI hV (fsuL0 T L ⊔ T)) :=
    ⟨autI_mono hV le_sup_left, (autI_mono hV le_top).trans (autI_top_le_normalizer hV hNM)⟩
  have hrow' : (∃ n : ℕ, 1 ≤ n ∧ BinaryNineTensor (autI hV (fsuL0 T L)) ⊤ ⊥ n) ∨
      MathieuCode24 (autI hV (fsuL0 T L)) ⊤ ⊥ ∨ MathieuCocode24 (autI hV (fsuL0 T L)) ⊤ ⊥ ∨
      (MathieuCode22 (autI hV (fsuL0 T L)) ⊤ ⊥ ∧
        autI hV (fsuL0 T L ⊔ T) = autI hV (fsuL0 T L)) := by
    rcases hrow with ⟨n, hn⟩ | hr | hr | hr
    · exact Or.inl ⟨n, hn.1, hn.2⟩
    · refine Or.inr (Or.inr (Or.inr ⟨hr, ?_⟩))
      have hle : autI hV T ≤ autI hV (fsuL0 T L) := by
        by_contra h
        exact hex ⟨hr, h⟩
      rw [autI_sup hV (le_sup_left.trans hN) (le_sup_right.trans hN)]
      exact sup_eq_left.mpr hle
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr (Or.inl hr))
  have h2 := hQ (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (autI hV (fsuL0 T L ⊔ T)) hover
    hrow'
  rcases theorem318_two_of_316 h316 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.sylow
      h318 with hq | ⟨hall, -⟩
  · exact absurd hq (not_le.mpr h2)
  · exact hall H hH

omit [Finite G] in
theorem isTISetIn_822 {V X : Subgroup G} (hVX : V ≤ X)
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) : IsTISetIn V X :=
  ⟨hVX, fun _ hg hgn => absurd (hXN hg) hgn⟩

theorem hyp28_822 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (h331 : Stmt3_3_1) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (hyp : Hyp7_0_2 G T L I) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) (h1 : ¬ fsuV T I ≤ pCoreOf 2 H) :
    E2.Hyp28 H T (H ⊓ fsuM T L) (fsuV T I) ∧ QuasithinUnique.CharTwo H ∧
      IsTISetIn (fsuV T I) (H ⊓ fsuM T L) ∧
      H ⊓ fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  obtain ⟨hmin, hsq, hchar, hHMN⟩ := setting_822 h37 h38 h39 h3228 h325 h331 hC58 h317 hyp hTL hH
  have hVT : fsuV T I ≤ T := fsuV_le_T hyp.fsu hV hN
  have hVHM : fsuV T I ≤ H ⊓ fsuM T L :=
    le_inf (hVT.trans hH.1.1) (hVT.trans (le_normalizer_conjClosure L T))
  have hVp : IsPGroup 2 ↥(fsuV T I) := B2F.isPGroup_of_isElemAbelian hV
  refine ⟨⟨hmin, hsq, hVT, le_sup_right.trans hN, hV,
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVHM hHMN hVp, fun hJ => h1 ?_⟩,
    hchar, isTISetIn_822 hVHM hHMN, hHMN⟩
  exact hmin.le_pCoreOf_of_isPGroup_of_le_kerIn hVp hJ

theorem wParam_pos_822 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h325 : Stmt3_2_5) (hin : Input8_1_2) (h711n : Stmt7_1_1_normal)
    (h756 : Stmt7_5_6_two) (h813 : Stmt8_1_3) (h755 : Input7_5_5) (htab : HTab82)
    (hcode : HCode82) (hcard : Mathieu.StmtH13Card) (hyp : Hyp7_0_2 G T L I)
    (h731 : Hyp7_3_1 T L I) [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Case8_2 T L I) :
    0 < wParam T (fsuV T I) := by
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hrow
  have hfw := lemma_7_5_1 hyp hV hN hNM
  obtain ⟨-, hT22, hT24⟩ := tab_82 (stmt7_4_1_of h37 h38 h39 hmod h325 hin) htab hyp h731 hTL
    hV hNM
  have hcode1 : ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) + 1 ≤ rParam (fsuV T I) →
      0 < wParam T (fsuV T I) := by
    intro hm2r
    refine pos_iff_ne_zero.mpr fun hw0 => ?_
    rw [hw0, add_zero] at hfw
    have h1 := hm2r.trans hfw
    have h2 : ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) < _ + 1 :=
      ENat.lt_add_one_iff (ENat.natCast_ne_top _) |>.mpr le_rfl
    exact absurd h1 (not_le.mpr h2)
  rcases hrow with ⟨n, hr⟩ | hr | hr | hr
  · have hnw : (n : ℕ∞) ≤ wParam T (fsuV T I) := h756 G T L I hyp h731 hc n hr
    have hn1 : (0 : ℕ∞) < n := by exact_mod_cast hr.1
    exact lt_of_lt_of_le hn1 hnw
  · obtain ⟨hm2, hr6⟩ := hT22 hr
    refine hcode1 (le_trans ?_ hr6)
    exact_mod_cast Nat.succ_le_succ hm2
  · obtain ⟨hm2, -, -, -⟩ := hT24 hr
    refine hcode1 (le_trans ?_
      (seven_le_rParam_82 h37 h38 h39 hmod h325 hin h755 htab hcode hcard hyp h731 hTL hV hr))
    exact_mod_cast Nat.succ_le_succ hm2
  · obtain ⟨-, -, hw2, -, -⟩ := h813 G T L I hyp h731 hc (Or.inr (Or.inr hr))
    rw [hw2]
    norm_num

theorem conj_le_centralizer_822 (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hw : 0 < wParam T (fsuV T I)) (i : G) (hiT : B6.conjSub i (fsuV T I) ≤ T) :
    B6.conjSub i (fsuV T I) ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  rw [conjSub_eq_conjSubgroup_82] at hiT ⊢
  exact conj_le_centralizer_of_le_normalizer hV (hypE322_of_fsu hyp.fsu hV hN) hw
    (hiT.trans (le_sup_right.trans hN))

end L822A

end CFSG.Quasithin.H13
