module

public import CFSG.Quasithin.Vol2.Ch3Sec1D12
public import CFSG.Quasithin.Background.SimsD1Four
public import CFSG.Quasithin.Background.SimsD1Transport

public section

namespace CFSG.Quasithin.SimsD1.FourGen

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.SimsD1.Transport

variable {G : Type} [Group G] {G₁ G₂ T V M₂ : Subgroup G}

theorem d14_general [Finite G₁] [Finite G₂]
    (h : D11Hyp G₁ G₂ T V M₂) (hVR₂ : V ≤ pCoreOf 2 G₂)
    (hchief : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1) :
    IsDualFFInt G₁ V h.reduced.2.2.1 ∨
    (((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).subgroupOf G₂).Normal ∧
      IsElemAbelian 2 (conjClosure V G₂) ∧
      ⁅conjClosure V G₂, twoResidual G₂⁆ ≤ centerOf (pCoreOf 2 G₂) ∧
      twoResidual G₂ = ⁅twoResidual G₂, thompsonJ (pCoreOf 2 G₁)⁆ ∧
      (¬ IsFFInt G₁ V h.reduced.2.2.1 → thompsonJ T = thompsonJ (pCoreOf 2 G₁)) ∧
      (∃ (I : Subgroup G) (hI : IsTwoReducedIn G₂ I),
        I ≤ conjClosure V G₂ ∧ IsFFInt G₂ I hI.2.2.1) ∧
      (Group.IsSolvable G₂ → CharTwo G₂ →
        IsSylowTwoOf (pCoreOf 2 G₁) (twoResidual G₂ ⊔ pCoreOf 2 G₁))) := by
  obtain ⟨F, _, _, ⟨e⟩⟩ := exists_emb (T := T) h.sylow₁.1 h.sylow₂.1
  have h' := d11Hyp_img e h
  have hV₁ : V ≤ G₁ := h.reduced.1
  have hVT : V ≤ T := h.V_le_T
  have hV₂ : V ≤ G₂ := hVT.trans e.le₂
  have hR₁ : pCoreOf 2 G₁ ≤ G₁ := CFSG.LieType.BorelTits.pCoreOf_le 2 G₁
  have hR₂ : pCoreOf 2 G₂ ≤ G₂ := CFSG.LieType.BorelTits.pCoreOf_le 2 G₂
  have hRT : pCoreOf 2 G₁ ≤ T := h.pCoreOf_le_T
  have hRG₂ : pCoreOf 2 G₁ ≤ G₂ := hRT.trans e.le₂
  have hJR : thompsonJ (pCoreOf 2 G₁) ≤ pCoreOf 2 G₁ := B6.thompsonJ_le _
  have hJT : thompsonJ T ≤ T := B6.thompsonJ_le _
  have hU₂ : conjClosure V G₂ ≤ G₂ := conjClosure_le_of_le hV₂ le_rfl
  have hO₂ : twoResidual G₂ ≤ G₂ := twoResidual_le G₂
  have hVeq : img e.ι₁ V = img e.ι₂ V := e.img_eq hVT
  have hRF₁ : pCoreOf 2 (img e.ι₁ G₁) = img e.ι₁ (pCoreOf 2 G₁) :=
    (img_pCoreOf e.inj₁ 2 le_rfl).symm
  have hReq : img e.ι₁ (pCoreOf 2 G₁) = img e.ι₂ (pCoreOf 2 G₁) := e.img_eq hRT
  have hRF₂ : pCoreOf 2 (img e.ι₂ G₂) = img e.ι₂ (pCoreOf 2 G₂) :=
    (img_pCoreOf e.inj₂ 2 le_rfl).symm
  have hU : conjClosure (img e.ι₁ V) (img e.ι₂ G₂) = img e.ι₂ (conjClosure V G₂) := by
    rw [hVeq, img_conjClosure hV₂ le_rfl]
  have hVR₂' : img e.ι₁ V ≤ pCoreOf 2 (img e.ι₂ G₂) := by
    rw [hVeq, hRF₂]
    exact img_mono hVR₂
  have hchief' : IsChiefSeriesFrom (img e.ι₂ G₂) (conjClosure (img e.ι₁ V) (img e.ι₂ G₂))
      (conjClosure (img e.ι₁ V) (img e.ι₂ G₂)) 1 := by
    rw [hU]
    exact (isChiefSeriesFrom_img_iff e.inj₂ le_rfl hU₂ hU₂ 1).2 hchief
  rcases Four.d14_finite h' hVR₂' hchief' with h1 | ⟨hn, hea, hcom, hres, hJ, hI, hsyl⟩
  ·
    exact Or.inl ((isDualFFInt_img_iff e.inj₁ le_rfl hV₁ h.reduced.2.2.1 h'.reduced.2.2.1).1 h1)
  refine Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hRF₁, hReq, hRF₂, ← img_inf e.inj₂] at hn
    exact (normal_img_iff e.inj₂ (inf_le_right.trans hR₂) le_rfl).1 hn
  · rw [hU] at hea
    exact (isElemAbelian_img_iff e.inj₂ hU₂ 2).1 hea
  · rw [hU, hRF₂, ← img_twoResidual e.inj₂ le_rfl, ← img_centerOf e.inj₂ hR₂,
      ← img_commutator hU₂ hO₂] at hcom
    exact (img_le_img_iff e.inj₂ (commutator_le_of_le hU₂ hO₂)).1 hcom
  · rw [hRF₁, hReq, ← img_thompsonJ e.inj₂ hRG₂, ← img_twoResidual e.inj₂ le_rfl,
      ← img_commutator hO₂ (hJR.trans hRG₂)] at hres
    exact (img_inj e.inj₂ hO₂ (commutator_le_of_le hO₂ (hJR.trans hRG₂))).1 hres
  · intro hnff
    have hJ' := hJ fun hff => hnff
      ((isFFInt_img_iff e.inj₁ le_rfl hV₁ h.reduced.2.2.1 h'.reduced.2.2.1).1 hff)
    rw [hRF₁, ← img_thompsonJ e.inj₁ e.le₁, ← img_thompsonJ e.inj₁ hR₁] at hJ'
    exact (img_inj e.inj₁ (hJT.trans e.le₁) (hJR.trans hR₁)).1 hJ'
  · obtain ⟨I₁, hI₁, hI₁U, hff⟩ := hI
    rw [hU] at hI₁U
    obtain ⟨I, hIU, rfl⟩ := exists_img_of_le e.inj₂ hU₂ hI₁U
    have hI₂ : I ≤ G₂ := hIU.trans hU₂
    have hIred : IsTwoReducedIn G₂ I := (isTwoReducedIn_img_iff e.inj₂ le_rfl hI₂).1 hI₁
    exact ⟨I, hIred, hIU,
      (isFFInt_img_iff e.inj₂ le_rfl hI₂ hIred.2.2.1 hI₁.2.2.1).1 hff⟩
  · intro hsolv hchar
    have hS := hsyl ((isSolvable_img_iff e.inj₂ le_rfl).2 hsolv)
      ((charTwo_img_iff e.inj₂ le_rfl).2 hchar)
    rw [hRF₁, hReq, ← img_twoResidual e.inj₂ le_rfl, ← img_sup hO₂ hRG₂] at hS
    exact (isSylowTwoOf_img_iff e.inj₂ hRG₂ (sup_le hO₂ hRG₂)).1 hS

end CFSG.Quasithin.SimsD1.FourGen
