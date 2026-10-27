module

public import CFSG.Quasithin.EmptyFaithful.S153D0Star

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I : Subgroup G} {t : G}

theorem CGS_le_of_eq (h113 : StageLemma14113) (h : Hyp153 G T Mc M) {R : Subgroup G}
    (hR : R = T ⊓ Subgroup.centralizer (VZ T M : Set G)) : CGS R ≤ M := by
  have hC : pCoreOf 2 (Y153 Mc M ⊔ T) = R := hR ▸ h.lemma_15_3_7_pCore h113
  have hYT : Y153 Mc M ⊔ T ≤ Subgroup.normalizer (R : Set G) := hC ▸ le_normalizer_pCoreOf 2 _
  have hU := h.lemma_15_3_7_unique h113
  have hRp : IsPGroup 2 R := hC ▸ pCoreOf_isPGroup 2 _
  refine iSup_le fun C => iSup_le fun hCR => iSup_le fun hC1 => iSup_le fun hchar => ?_
  have hNC : Y153 Mc M ⊔ T ≤ Subgroup.normalizer (C : Set G) :=
    hYT.trans (normalizer_le_normalizer_of_characteristic_subgroupOf hCR hchar)
  have hCp : IsPGroup 2 C := hRp.to_le hCR
  have hCO : C ≤ pCoreOf 2 (Subgroup.normalizer (C : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hCp
  exact le_of_isUniqueM hU ⟨hNC, fun hb => hC1 (le_bot_iff.mp (hb ▸ hCO))⟩

theorem R_ne_bot_of_eq (h : Hyp153 G T Mc M) {R : Subgroup G}
    (hR : R = T ⊓ Subgroup.centralizer (VZ T M : Set G)) : R ≠ ⊥ := by
  intro hbot
  have hVR : VZ T M ≤ R := by
    rw [hR]
    refine le_inf h.VZ_le_T fun v hv => Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    exact B2F.isElemAbelian_comm h.elemAbelian hw hv
  have hV : VZ T M = ⊥ := le_bot_iff.mp (hbot ▸ hVR)
  have h16 := h.card_VZ
  rw [hV, Subgroup.card_bot] at h16
  omega

theorem facts15311_of_partial (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) {I : Subgroup G} (hI : IsHPlus Yp (Sgp153 T V₁) M I)
    (hstruct : IsElemAbelianOfRank 3 2 (OTwoQuot Yp) ∨ IsPOnePlusTwo 3 (OTwoQuot Yp))
    (hR : R153 T V₁ Yp = T ⊓ Subgroup.centralizer (VZ T M : Set G))
    (hJ : ¬ autOn (thompsonJ I) (UI153 T I) ≤ autOn (M ⊓ I) (UI153 T I)) :
    Facts15311 T M V₁ Yp I := by
  have hsyl := h.lemma_15_3_11_one h11 h113 hI
  have hnorm := h.lemma_15_3_11_four h113 hI
  have hcgs : CGS (R153 T V₁ Yp) ≤ M := CGS_le_of_eq h113 h.hyp hR
  have hR1 : R153 T V₁ Yp ≠ ⊥ := R_ne_bot_of_eq h.hyp hR
  have hRM : Subgroup.normalizer ((R153 T V₁ Yp : Subgroup G) : Set G) ≤ M :=
    (normalizer_le_CGS le_rfl hR1 (by rw [Subgroup.subgroupOf_self]; infer_instance)).trans hcgs
  obtain ⟨hsylR, hrad⟩ := sylow_radical_of_normalizer_le h.oTwoUpper_eq.symm
    (le_sup_left.trans hI.1.1) hsyl (inf_le_left.trans h.hyp.T_le) hnorm hR1 hRM
  exact
    { sylow := hsyl
      cent_le := h.lemma_15_3_11_two h113 hI
      norm_eq := hnorm
      struct_Yp := hstruct
      R_eq := hR
      radical := hrad
      sylow_R := hsylR
      cgs := hcgs
      theta := h.theta_eq h113 hI
      star_norm := h.star_norm h113 hI
      star_lt := h.star_lt h113 hI
      star_ne := h.star_ne h113 hI
      J_not_le := hJ }

end S153D

end CFSG.Quasithin
