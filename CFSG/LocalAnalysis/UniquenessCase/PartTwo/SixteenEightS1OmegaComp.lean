module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1OmegaFstar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1OmegaCSig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1OmegaCLay
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1OmegaCAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1OmegaCUp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OmegaPlusFourSquare
public import CFSG.GH74.GLS.Stage1.Main.P49HMain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

noncomputable def s16e_omf_N (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L : Subgroup G) : Subgroup ↥(Mbar D.M V₀ V hV) :=
  (lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)

theorem s16e_omc_N_normal (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hs : s15 D.M V₀ V hV L = 1) : (s16e_omf_N D V₀ V hV L).Normal := by
  rw [s16e_omf_N]
  refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
  intro g hg
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (lBar_conj_eq_of_s15_eq_one hs hg)

theorem s16e_omc_N_equiv_alt_five (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hL : L ≤ D.M) (h : IsOmegaPlus ↥(lBar V₀ V hV L) 4 2) :
    Nonempty (↥(s16e_omf_N D V₀ V hV L) ≃*
      alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := s16e_omc_equiv_alt_five_of_isOmegaPlus h
  have hle : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hL
  exact ⟨(Subgroup.subgroupOfEquivOfLe hle).trans e⟩

theorem s16e_omf_comp_layer (D : Data G) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (h : Case162_7 D V₀ V hV L) :
    s16e_omf_N D V₀ V hV L ≤ CFSG.layer ↥(Mbar D.M V₀ V hV) := by
  haveI := s16e_omc_N_normal D hV h.2.2
  obtain ⟨e⟩ := s16e_omc_N_equiv_alt_five D hV hset.hyp151.le h.1
  exact s16e_omc_le_layer_of_equiv_alt_five e

theorem s16e_omf_comp_centralizer (D : Data G) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (h : Case162_7 D V₀ V hV L) :
    Group.IsNilpotent ↥(Subgroup.centralizer
        (s16e_omf_N D V₀ V hV L : Set ↥(Mbar D.M V₀ V hV))) ∧
      Nonempty (↥(Subgroup.centralizer
          (s16e_omf_N D V₀ V hV L : Set ↥(Mbar D.M V₀ V hV))) ≃* Multiplicative (ZMod 3)) := by
  haveI := s16e_omc_N_normal D hV h.2.2
  obtain ⟨e⟩ := s16e_omc_N_equiv_alt_five D hV hset.hyp151.le h.1
  have hne : Subgroup.centralizer (s16e_omf_N D V₀ V hV L : Set ↥(Mbar D.M V₀ V hV)) ≠ ⊥ :=
    s16e_omc_centralizer_ne_bot e
      (s16e_omc_dvd_card_mBar D hx h4 h61 h127 h1217 hV hset hL hconc h)
  haveI : Nontrivial ↥(Subgroup.centralizer
      (s16e_omf_N D V₀ V hV L : Set ↥(Mbar D.M V₀ V hV))) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 hne
  obtain ⟨K, hKf, hKfin, hK4, f, hf⟩ :=
    s16e_omc_centralizer_embeds_units_mBar D hx h4 h61 h127 h1217 hV hset hL hconc h
  exact s16e_omc_nilpotent_equiv_zmod_three hK4 f hf

theorem s16e_omf_comp_center_bot (D : Data G) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (h : Case162_7 D V₀ V hV L) :
    s16e_omf_N D V₀ V hV L ⊓ Subgroup.centralizer
        (s16e_omf_N D V₀ V hV L : Set ↥(Mbar D.M V₀ V hV)) = ⊥ := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eΩ⟩⟩ := h.1
  letI := hKf
  letI := hKfin
  haveI hKchar : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hKcard
  have h4 : 4 ≤ Nat.card K := by rw [hKcard]; norm_num
  obtain ⟨e4⟩ := nonempty_statedOmegaFour_mulEquiv_prod (K := K) h4
  have hle : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hset.hyp151.le
  let e : s16e_omf_N D V₀ V hV L ≃* ↥(StatedSL 2 K) × ↥(StatedSL 2 K) :=
    (Subgroup.subgroupOfEquivOfLe hle).trans
      (eΩ.trans ((statedProjStatedOmegaFourEquiv K).trans e4))
  have hSL : Subgroup.center ↥(StatedSL 2 K) = ⊥ := by
    rw [CFSG.GH74.L5U5.center_statedSL_eq (F := K) 2]
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot
  have hcX : Subgroup.center (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) = ⊥ := by
    simp [Subgroup.center_prod (G := ↥(StatedSL 2 K)) (H := ↥(StatedSL 2 K)), hSL]
  have hcN : Subgroup.center (s16e_omf_N D V₀ V hV L) = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    have hz' : e z ∈ Subgroup.center (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_center_iff.1 hz y'
    rw [hcX] at hz'
    have hz1 : e z = 1 := Subgroup.mem_bot.1 hz'
    have hzN : z = 1 := e.injective (by simpa using hz1)
    simpa using hzN
  rw [← CFSG.GH74.GLS.Stage1.Thm3.Sec6.P49H.map_center_eq_inf_centralizer
    (s16e_omf_N D V₀ V hV L), hcN, Subgroup.map_bot]

theorem s16e_omf_fstarBar_equiv (D : Data G) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (h : Case162_7 D V₀ V hV L) :
    Nonempty (↥(fstarBar D.M V₀ V hV) ≃*
      (Multiplicative (ZMod 3) × ↥(lBar V₀ V hV L))) := by
  haveI hNnorm : (s16e_omf_N D V₀ V hV L).Normal := by
    rw [s16e_omf_N]
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (lBar_conj_eq_of_s15_eq_one h.2.2 hg)
  obtain ⟨hCnil, hCiso⟩ := s16e_omf_comp_centralizer D hx h4 h61 h127 h1217 hV hset hL hconc h
  have hFstar := s16e_omf_generalizedFitting_eq_sup_centralizer
    (s16e_omf_comp_layer D hx h4 h61 h127 h1217 hV hset hL hconc h) hCnil
  obtain ⟨eF⟩ := s16e_omf_nonempty_mulEquiv_centralizer_prod hFstar
    (s16e_omf_comp_center_bot D hx h4 h61 h127 h1217 hV hset hL hconc h)
  obtain ⟨eC⟩ := hCiso
  have hle : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hset.hyp151.le
  have hfb : fstarBar D.M V₀ V hV =
      (CFSG.generalizedFitting ↥(Mbar D.M V₀ V hV)).map (Mbar D.M V₀ V hV).subtype := by
    simp only [fstarBar, Fstar, CFSG.Adapters.genFittingFStar_eq_foundations]
  have e1 : ↥(fstarBar D.M V₀ V hV) ≃*
      ↥(CFSG.generalizedFitting ↥(Mbar D.M V₀ V hV)) := by
    rw [hfb]
    exact (Subgroup.equivMapOfInjective _ (Mbar D.M V₀ V hV).subtype
      (Mbar D.M V₀ V hV).subtype_injective).symm
  let eN : ↥(s16e_omf_N D V₀ V hV L) ≃* ↥(lBar V₀ V hV L) :=
    Subgroup.subgroupOfEquivOfLe hle
  exact ⟨e1.trans (eF.trans (MulEquiv.prodCongr eC eN))⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
