module

public import CFSG.Quasithin.Background.SimsD1Twelve
public import CFSG.Quasithin.Background.SimsD1Transport

public section

namespace CFSG.Quasithin.SimsD1.TwelveGen

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.SimsD1.Transport

variable {G : Type} [Group G] {G₁ G₂ T V M₂ : Subgroup G}

theorem d12_general (hB : B69One) [hf₁ : Finite G₁] [hf₂ : Finite G₂]
    (h : D11Hyp G₁ G₂ T V M₂)
    (hq : (1 : WithTop ℚ) < qSub G₁ V hf₁ h.reduced.1 h.reduced.2.2.1) :
    (V ≤ pCoreOf 2 G₂ → IsElemAbelian 2 (conjClosure V G₂)) ∧
    (thompsonJ T = thompsonJ (pCoreOf 2 G₁) ∧
      thompsonJ (pCoreOf 2 G₁) = thompsonJ (pCoreOf 2 G₁ ⊔ pCoreOf 2 G₂)) ∧
    (¬ G₂ ≤ Subgroup.normalizer (T : Set G) ∧ ¬ thompsonJ (pCoreOf 2 G₁) ≤ pCoreOf 2 G₂) ∧
    IsMinParabolicOf G₂ G₂ ∧
    (∀ (W : Subgroup G) (hWG : W ≤ G₂) (hWE : IsElemAbelian 2 W),
      G₂ ≤ Subgroup.normalizer (W : Set G) → W ≤ pCoreOf 2 G₂ →
      pCoreOf 2 G₂ ≤ Subgroup.centralizer (W : Set G) →
      G₂ ⊓ Subgroup.centralizer (W : Set G) ≤ M₂ →
      IsTwoReducedIn G₂ W ∧
        (CFSG.SectionRank.IsSQTKCat ↥G₂ → (1 : WithTop ℚ) ≤ qSub G₂ W hf₂ hWG hWE)) := by
  obtain ⟨F, _, _, ⟨e⟩⟩ := exists_emb (T := T) h.sylow₁.1 h.sylow₂.1
  have h' := d11Hyp_img e h
  have hV₁ : V ≤ G₁ := h.reduced.1
  have hVT : V ≤ T := h.V_le_T
  have hV₂ : V ≤ G₂ := hVT.trans e.le₂
  have hR₁ : pCoreOf 2 G₁ ≤ G₁ := CFSG.LieType.BorelTits.pCoreOf_le 2 G₁
  have hR₂ : pCoreOf 2 G₂ ≤ G₂ := CFSG.LieType.BorelTits.pCoreOf_le 2 G₂
  have hRT : pCoreOf 2 G₁ ≤ T := h.pCoreOf_le_T
  have hRG₂ : pCoreOf 2 G₁ ≤ G₂ := hRT.trans e.le₂
  have hRR₂ : pCoreOf 2 G₁ ⊔ pCoreOf 2 G₂ ≤ G₂ := sup_le hRG₂ hR₂
  have hJR : thompsonJ (pCoreOf 2 G₁) ≤ pCoreOf 2 G₁ := B6.thompsonJ_le _
  have hJT : thompsonJ T ≤ T := B6.thompsonJ_le _
  have hU₂ : conjClosure V G₂ ≤ G₂ := conjClosure_le_of_le hV₂ le_rfl
  have hVeq : img e.ι₁ V = img e.ι₂ V := e.img_eq hVT
  have hTeq : img e.ι₁ T = img e.ι₂ T := e.img_eq le_rfl
  have hRF₁ : pCoreOf 2 (img e.ι₁ G₁) = img e.ι₁ (pCoreOf 2 G₁) :=
    (img_pCoreOf e.inj₁ 2 le_rfl).symm
  have hReq : img e.ι₁ (pCoreOf 2 G₁) = img e.ι₂ (pCoreOf 2 G₁) := e.img_eq hRT
  have hRF₂ : pCoreOf 2 (img e.ι₂ G₂) = img e.ι₂ (pCoreOf 2 G₂) :=
    (img_pCoreOf e.inj₂ 2 le_rfl).symm
  have hnff : ¬ IsFFInt (img e.ι₁ G₁) (img e.ι₁ V) h'.reduced.2.2.1 := by
    rw [isFFInt_iff_qInt_le_one,
      qInt_img e.inj₁ le_rfl hV₁ hf₁ h.reduced.2.2.1 h'.reduced.2.2.1, not_le]
    exact hq
  obtain ⟨c1, ⟨c2, c2'⟩, ⟨c3, c3'⟩, c4, c5⟩ := SimsD1.Twelve.d12_finite hB h' hnff
  refine ⟨fun hle => ?_, ⟨?_, ?_⟩, ⟨fun hn => c3 ?_, fun hle => c3' ?_⟩, ?_, ?_⟩
  ·
    have hc := c1 (by rw [hVeq, hRF₂]; exact img_mono hle)
    rw [hVeq, ← img_conjClosure (ι := e.ι₂) hV₂ le_rfl] at hc
    exact (isElemAbelian_img_iff e.inj₂ hU₂ 2).1 hc
  ·
    rw [hRF₁, ← img_thompsonJ e.inj₁ e.le₁, ← img_thompsonJ e.inj₁ hR₁] at c2
    exact (img_inj e.inj₁ (hJT.trans e.le₁) (hJR.trans hR₁)).1 c2
  ·
    rw [hRF₁, hReq, hRF₂, ← img_sup (ι := e.ι₂) hRG₂ hR₂, ← img_thompsonJ e.inj₂ hRG₂,
      ← img_thompsonJ e.inj₂ hRR₂] at c2'
    exact (img_inj e.inj₂ (hJR.trans hRG₂) ((B6.thompsonJ_le _).trans hRR₂)).1 c2'
  ·
    rw [hTeq]
    exact (le_normalizer_img_iff e.inj₂ le_rfl e.le₂).2 hn
  ·
    rw [hRF₁, hReq, hRF₂, ← img_thompsonJ e.inj₂ hRG₂]
    exact img_mono hle
  ·
    exact (isMinParabolicOf_img_iff e.inj₂ le_rfl le_rfl).1 c4
  ·
    intro W hWG hWE hG₂W hWR hRC hCM
    have hWE' : IsElemAbelian 2 (img e.ι₂ W) := (isElemAbelian_img_iff e.inj₂ hWG 2).2 hWE
    obtain ⟨hred, hq1⟩ := c5 (img e.ι₂ W) (img_mono hWG) hWE'
      ((le_normalizer_img_iff e.inj₂ le_rfl hWG).2 hG₂W)
      (by rw [hRF₂]; exact img_mono hWR)
      (by rw [hRF₂]; exact (le_centralizer_img_iff e.inj₂ hR₂ hWG).2 hRC)
      (by rw [← img_inf_centralizer e.inj₂ le_rfl hWG]; exact img_mono hCM)
    refine ⟨(isTwoReducedIn_img_iff e.inj₂ le_rfl hWG).1 hred, fun hcat => ?_⟩
    rw [← qInt_img e.inj₂ le_rfl hWG hf₂ hWE hWE']
    exact hq1 ((isSQTKCat_img_iff e.inj₂ le_rfl).2 hcat)

end CFSG.Quasithin.SimsD1.TwelveGen
