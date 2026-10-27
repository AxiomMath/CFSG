module

public import CFSG.Quasithin.EmptyFaithful.S153Plus
public import CFSG.Quasithin.EmptyFaithful.S153YCases

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem charTwo_inf (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) {I : Subgroup G}
    (hSI : Sgp153 T V₁ ≤ I) : CharTwo (M ⊓ I) := by
  obtain ⟨S₀, hS₀⟩ := h.qtfe.exists_sylow
  have hS₀M : (S₀ : Subgroup G) ≤ M := hS₀ ▸ h.T_le
  have hCM : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    h.qtfe.qtke.2.1 M h.inM.1.1 ⟨S₀, hS₀M⟩
  have hO2T : pCoreOf 2 M ≤ T := by
    have := pCoreOf_two_le_sylow M S₀ hS₀M
    rwa [hS₀] at this
  have hO2C : pCoreOf 2 M ≤ Subgroup.centralizer (VZ T M : Set G) :=
    h.hyp14117.pCoreOf_le_centralizer
  have hO2S : pCoreOf 2 M ≤ Sgp153 T V₁ :=
    le_inf hO2T ((hO2C.trans (Subgroup.centralizer_le D.le₁)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hO2I : pCoreOf 2 M ≤ M ⊓ I := le_inf (pCoreOf_le 2 M) (hO2S.trans hSI)
  have hMI : M ⊓ I ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    inf_le_left.trans (le_normalizer_pCoreOf 2 M)
  have hle : pCoreOf 2 M ≤ pCoreOf 2 (M ⊓ I) :=
    le_pCoreOf_of_le_normalizer 2 hO2I hMI (pCoreOf_isPGroup 2 M)
  intro x hx
  have hxC : x ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) := Subgroup.centralizer_le hle hx.2
  exact hle (hCM ⟨hx.1.1, hxC⟩)

theorem R153_Y153 (h113 : StageLemma14113) (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) :
    pCoreOf 2 (Y153 Mc M ⊔ Sgp153 T V₁) = T ⊓ Subgroup.centralizer (VZ T M : Set G) ∧
      Y153 Mc M ⊔ T ≤ Subgroup.normalizer
        (pCoreOf 2 (Y153 Mc M ⊔ Sgp153 T V₁) : Set G) := by
  set S : Subgroup G := Sgp153 T V₁ with hSdef
  have hST : S ≤ T := inf_le_left
  have hTY : T ≤ Subgroup.normalizer (Y153 Mc M : Set G) :=
    h.T_le.trans (le_normalizer_Y153 Mc M)
  have hTS : T ≤ Subgroup.normalizer (S : Set G) := h.T_le_normalizer_Sgp153 D
  have hYS : Y153 Mc M ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 (Y153 Mc M ⊔ S) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hTYS : T ≤ Subgroup.normalizer ((Y153 Mc M ⊔ S : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_sup (Y153 Mc M) S ⟨hTY hg, hTS hg⟩
  have hTN : T ≤ Subgroup.normalizer (pCoreOf 2 (Y153 Mc M ⊔ S) : Set G) :=
    hTYS.trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hYT : Y153 Mc M ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (Y153 Mc M ⊔ S) : Set G) :=
    sup_le (le_sup_left.trans hYS) hTN
  have hC : pCoreOf 2 (Y153 Mc M ⊔ T) = T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
    h.lemma_15_3_7_pCore h113
  refine ⟨le_antisymm ?_ ?_, hYT⟩
  · have h1 : pCoreOf 2 (Y153 Mc M ⊔ S) ≤ pCoreOf 2 (Y153 Mc M ⊔ T) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (sup_le_sup_left hST _)) hYT
        (pCoreOf_isPGroup 2 _)
    rwa [hC] at h1
  · have hCS : T ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ S :=
      inf_le_inf_left T ((Subgroup.centralizer_le D.le₁).trans
        (Subgroup.centralizer_le_normalizer _))
    have hn : Y153 Mc M ⊔ S ≤ Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G) := by
      have := le_normalizer_pCoreOf 2 (Y153 Mc M ⊔ T)
      rw [hC] at this
      exact (sup_le_sup_left hST _).trans this
    exact le_pCoreOf_of_le_normalizer 2 (hCS.trans le_sup_right) hn
      (h.qtfe.sylow.1.to_le inf_le_left)

theorem CGS_R153_Y153_le (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) :
    CGS (pCoreOf 2 (Y153 Mc M ⊔ Sgp153 T V₁)) ≤ M := by
  obtain ⟨-, hYT⟩ := h.R153_Y153 h113 D
  have hU := h.lemma_15_3_7_unique h113
  refine iSup_le fun C => iSup_le fun hCR => iSup_le fun hC1 => iSup_le fun hchar => ?_
  have hNC : Y153 Mc M ⊔ T ≤ Subgroup.normalizer (C : Set G) :=
    hYT.trans (normalizer_le_normalizer_of_characteristic_subgroupOf hCR hchar)
  have hCp : IsPGroup 2 C := (pCoreOf_isPGroup 2 _).to_le hCR
  have hCO : C ≤ pCoreOf 2 (Subgroup.normalizer (C : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hCp
  exact le_of_isUniqueM hU ⟨hNC, fun hb => hC1 (le_bot_iff.mp (hb ▸ hCO))⟩

end Hyp153

namespace Hyp15310

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem lemma_15_3_11_five_case_one (h113 : StageLemma14113)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (hY : Yp = Y153 Mc M) :
    (IsElemAbelianOfRank 3 2 (OTwoQuot Yp) ∨ IsPOnePlusTwo 3 (OTwoQuot Yp)) ∧
      R153 T V₁ Yp = T ⊓ Subgroup.centralizer (VZ T M : Set G) ∧
      Yp ⊔ T ≤ Subgroup.normalizer (R153 T V₁ Yp : Set G) ∧ CGS (R153 T V₁ Yp) ≤ M := by
  subst hY
  obtain ⟨h1, h2⟩ := h.hyp.R153_Y153 h113 h.decomp
  refine ⟨?_, h1, h2, h.hyp.CGS_R153_Y153_le h113 h.decomp⟩
  rcases h.hyp.lemma_15_3_7_cases h113 with ⟨-, hE⟩ | ⟨hP, -⟩
  · exact Or.inl hE
  · exact Or.inr hP

end Hyp15310

end CFSG.Quasithin
