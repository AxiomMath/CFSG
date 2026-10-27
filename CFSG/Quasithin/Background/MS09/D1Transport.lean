module

public import CFSG.Quasithin.Background.MS09.D1General
public import CFSG.Quasithin.Background.SimsD1ThreeGen

public section

namespace CFSG.Quasithin.MS09

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.SimsD1.Transport
  CFSG.Quasithin.SimsD1.ThreeGen

variable {G : Type} [Group G] {G₁ G₂ T V M₂ : Subgroup G}

theorem d12_five_general [hf₁ : Finite G₁] [hf₂ : Finite G₂] (h : D11Hyp G₁ G₂ T V M₂)
    (hq : (1 : WithTop ℚ) < qSub G₁ V hf₁ h.reduced.1 h.reduced.2.2.1)
    (W : Subgroup G) (hWG : W ≤ G₂) (hWE : IsElemAbelian 2 W)
    (hG₂W : G₂ ≤ Subgroup.normalizer (W : Set G)) (hWR : W ≤ pCoreOf 2 G₂)
    (hRC : pCoreOf 2 G₂ ≤ Subgroup.centralizer (W : Set G))
    (hCM : G₂ ⊓ Subgroup.centralizer (W : Set G) ≤ M₂) :
    (1 : WithTop ℚ) ≤ qSub G₂ W hf₂ hWG hWE := by
  obtain ⟨F, _, _, ⟨e⟩⟩ := exists_emb (T := T) h.sylow₁.1 h.sylow₂.1
  have h' := d11Hyp_img e h
  have hR₂ : pCoreOf 2 G₂ ≤ G₂ := CFSG.LieType.BorelTits.pCoreOf_le 2 G₂
  have hRF₂ : pCoreOf 2 (img e.ι₂ G₂) = img e.ι₂ (pCoreOf 2 G₂) :=
    (img_pCoreOf e.inj₂ 2 le_rfl).symm
  have hnff : ¬ IsFFInt (img e.ι₁ G₁) (img e.ι₁ V) h'.reduced.2.2.1 := by
    rw [isFFInt_iff_qInt_le_one,
      qInt_img e.inj₁ le_rfl h.reduced.1 hf₁ h.reduced.2.2.1 h'.reduced.2.2.1, not_le]
    exact hq
  have hWE' : IsElemAbelian 2 (img e.ι₂ W) := (isElemAbelian_img_iff e.inj₂ hWG 2).2 hWE
  rw [← qInt_img e.inj₂ le_rfl hWG hf₂ hWE hWE']
  exact one_le_qInt_of_minParabolic (h'.minParabolic hnff) hWE'
    ((le_normalizer_img_iff e.inj₂ le_rfl hWG).2 hG₂W)
    (by rw [hRF₂]; exact img_mono hWR)
    (by rw [hRF₂]; exact (le_centralizer_img_iff e.inj₂ hR₂ hWG).2 hRC)
    (by rw [← img_inf_centralizer e.inj₂ le_rfl hWG]; exact img_mono hCM)

theorem d13_one_three_general [hf₁ : Finite G₁] [Finite G₂] (h : D11Hyp G₁ G₂ T V M₂)
    (hq : (1 : WithTop ℚ) < qSub G₁ V hf₁ h.reduced.1 h.reduced.2.2.1)
    (hVR₂ : V ≤ pCoreOf 2 G₂) (c : ℕ) (hc : 2 ≤ c)
    (hser : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) c) :
    qSub G₁ V hf₁ h.reduced.1 h.reduced.2.2.1 ≤ 2 ∧
    (qSub G₁ V hf₁ h.reduced.1 h.reduced.2.2.1 = 2 →
      c = 2 ∧
      ∀ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2 G₁) A →
        (⁅⁅conjClosure V G₂, A⁆, A⁆ = ⊥ ∧ ⁅conjClosure V G₂, A⁆ ≠ ⊥) →
        2 * padicValNat 2 ((A ⊓ pCoreOf 2 G₂).relIndex A) =
            padicValNat 2 ((conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G)).relIndex
              (conjClosure V G₂)) ∧
          padicValNat 2 ((conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G)).relIndex
              (conjClosure V G₂)) =
            2 * padicValNat 2 ((A ⊓ pCoreOf 2 G₂ ⊓
              Subgroup.centralizer (conjClosure V G₂ : Set G)).relIndex (A ⊓ pCoreOf 2 G₂)) ∧
          (∀ g ∈ G₂, ⁅V.map (MulAut.conj g⁻¹).toMonoidHom, A ⊓ pCoreOf 2 G₂⁆ ≠ ⊥ →
            2 * padicValNat 2 ((A ⊓ pCoreOf 2 G₂ ⊓
                Subgroup.centralizer (V.map (MulAut.conj g⁻¹).toMonoidHom : Set G)).relIndex
                  (A ⊓ pCoreOf 2 G₂)) =
              padicValNat 2 ((V.map (MulAut.conj g⁻¹).toMonoidHom ⊓
                Subgroup.centralizer ((A ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G)).relIndex
                  (V.map (MulAut.conj g⁻¹).toMonoidHom))) ∧
          (∀ L N : Subgroup G, IsChiefStep G₂ (conjClosure V G₂) L N → ¬ IsCentralStep G₂ L N →
            padicValNat 2 ((A ⊓ pCoreOf 2 G₂).relIndex A) =
              padicValNat 2 ((SimsD1.Three.secFix A N L).relIndex N)) ∧
          conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G) =
            conjClosure V G₂ ⊓
              Subgroup.centralizer ((A ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G)) := by
  obtain ⟨F, _, _, ⟨e⟩⟩ := exists_emb (T := T) h.sylow₁.1 h.sylow₂.1
  have h' := d11Hyp_img e h
  have hV₁ : V ≤ G₁ := h.reduced.1
  have hVT : V ≤ T := h.V_le_T
  have hV₂ : V ≤ G₂ := hVT.trans e.le₂
  have hR₁ : pCoreOf 2 G₁ ≤ G₁ := CFSG.LieType.BorelTits.pCoreOf_le 2 G₁
  have hR₂ : pCoreOf 2 G₂ ≤ G₂ := CFSG.LieType.BorelTits.pCoreOf_le 2 G₂
  have hRT : pCoreOf 2 G₁ ≤ T := h.pCoreOf_le_T
  have hU₂ : conjClosure V G₂ ≤ G₂ := conjClosure_le_of_le hV₂ le_rfl
  have hVeq : img e.ι₁ V = img e.ι₂ V := e.img_eq hVT
  have hRF₁ : pCoreOf 2 (img e.ι₁ G₁) = img e.ι₁ (pCoreOf 2 G₁) :=
    (img_pCoreOf e.inj₁ 2 le_rfl).symm
  have hRF₂ : pCoreOf 2 (img e.ι₂ G₂) = img e.ι₂ (pCoreOf 2 G₂) :=
    (img_pCoreOf e.inj₂ 2 le_rfl).symm
  have hU : conjClosure (img e.ι₁ V) (img e.ι₂ G₂) = img e.ι₂ (conjClosure V G₂) := by
    rw [hVeq, img_conjClosure hV₂ le_rfl]
  have hq' : qInt (img e.ι₁ G₁) (img e.ι₁ V) h'.reduced.2.2.1 =
      qSub G₁ V hf₁ h.reduced.1 h.reduced.2.2.1 :=
    qInt_img e.inj₁ le_rfl hV₁ hf₁ h.reduced.2.2.1 h'.reduced.2.2.1
  have hnff' : ¬ IsFFInt (img e.ι₁ G₁) (img e.ι₁ V) h'.reduced.2.2.1 := by
    rw [isFFInt_iff_qInt_le_one, hq']
    exact not_le.mpr hq
  have hVR₂' : img e.ι₁ V ≤ pCoreOf 2 (img e.ι₂ G₂) := by
    rw [hVeq, hRF₂]
    exact img_mono hVR₂
  have hser' : IsChiefSeriesFrom (img e.ι₂ G₂) (conjClosure (img e.ι₁ V) (img e.ι₂ G₂))
      (conjClosure (img e.ι₁ V) (img e.ι₂ G₂)) c := by
    rw [hU]
    exact (isChiefSeriesFrom_img_iff e.inj₂ le_rfl hU₂ hU₂ c).2 hser
  obtain ⟨hF1, hF3⟩ := d13_one_three_finite h' hnff' hVR₂' hc hser'
  refine ⟨hq'.ge.trans hF1, fun hq2 => ?_⟩
  obtain ⟨hc2, hall⟩ := hF3 (hq'.trans hq2)
  refine ⟨hc2, fun A hA hAq => ?_⟩
  have hAR : A ≤ pCoreOf 2 G₁ := hA.1
  have hAT : A ≤ T := hAR.trans hRT
  have hA₂ : A ≤ G₂ := hAT.trans e.le₂
  have hB₂ : A ⊓ pCoreOf 2 G₂ ≤ G₂ := inf_le_right.trans hR₂
  have hUA₂ : conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G) ≤ G₂ := inf_le_left.trans hU₂
  have hmax : IsMaxElemAbelian (pCoreOf 2 (img e.ι₁ G₁)) (img e.ι₁ A) := by
    rw [hRF₁]
    exact (isMaxElemAbelian_img_iff e.inj₁ hR₁ (hAR.trans hR₁)).2 hA
  have hquadF : ⁅⁅conjClosure (img e.ι₁ V) (img e.ι₂ G₂), img e.ι₁ A⁆, img e.ι₁ A⁆ = ⊥ ∧
      ⁅conjClosure (img e.ι₁ V) (img e.ι₂ G₂), img e.ι₁ A⁆ ≠ ⊥ := by
    rw [hU, e.img_eq hAT]
    exact (quad_img_iff e.inj₂ hU₂ hA₂).2 hAq
  obtain ⟨E1, E2, E3, E4, E5⟩ := hall (img e.ι₁ A) hmax hquadF
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hU, e.img_eq hAT, hRF₂, ← img_inf e.inj₂, relIndex_img e.inj₂ hB₂ hA₂,
      ← img_inf_centralizer e.inj₂ hU₂ hA₂, relIndex_img e.inj₂ hUA₂ hU₂] at E1
    exact E1
  · rw [hU, e.img_eq hAT, hRF₂, ← img_inf e.inj₂, ← img_inf_centralizer e.inj₂ hU₂ hA₂,
      ← img_inf_centralizer e.inj₂ hB₂ hU₂, relIndex_img e.inj₂ hUA₂ hU₂,
      relIndex_img e.inj₂ (inf_le_left.trans hB₂) hB₂] at E2
    exact E2
  · intro g hg hne
    have hVg₂ : V.map (MulAut.conj g⁻¹).toMonoidHom ≤ G₂ := map_conj_le hV₂ hg
    have hVg : img e.ι₂ (V.map (MulAut.conj g⁻¹).toMonoidHom) =
        (img e.ι₂ V).map (MulAut.conj (e.ι₂ ⟨g, hg⟩)⁻¹).toMonoidHom := img_conj' hV₂ hg
    have hgF : e.ι₂ ⟨g, hg⟩ ∈ img e.ι₂ G₂ := ⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    have hneF : ⁅(img e.ι₁ V).map (MulAut.conj (e.ι₂ ⟨g, hg⟩)⁻¹).toMonoidHom,
        img e.ι₁ A ⊓ pCoreOf 2 (img e.ι₂ G₂)⁆ ≠ ⊥ := by
      rw [hVeq, ← hVg, e.img_eq hAT, hRF₂, ← img_inf e.inj₂, ← img_commutator hVg₂ hB₂, ne_eq,
        img_eq_bot_iff e.inj₂ (commutator_le_of_le hVg₂ hB₂)]
      exact hne
    have E := E3 (e.ι₂ ⟨g, hg⟩) hgF hneF
    rw [hVeq, ← hVg, e.img_eq hAT, hRF₂, ← img_inf e.inj₂,
      ← img_inf_centralizer e.inj₂ hB₂ hVg₂, ← img_inf_centralizer e.inj₂ hVg₂ hB₂,
      relIndex_img e.inj₂ (inf_le_left.trans hB₂) hB₂,
      relIndex_img e.inj₂ (inf_le_left.trans hVg₂) hVg₂] at E
    exact E
  · intro L N hs hnc
    have hN₂ : N ≤ G₂ := hs.1.1.trans hU₂
    have hL₂ : L ≤ G₂ := hs.2.1.1.trans hU₂
    have hs' : IsChiefStep (img e.ι₂ G₂) (conjClosure (img e.ι₁ V) (img e.ι₂ G₂))
        (img e.ι₂ L) (img e.ι₂ N) := by
      rw [hU]
      exact (isChiefStep_img_iff e.inj₂ le_rfl hU₂ hL₂ hN₂).2 hs
    have hnc' : ¬ IsCentralStep (img e.ι₂ G₂) (img e.ι₂ L) (img e.ι₂ N) := fun h0 =>
      hnc ((isCentralStep_img_iff e.inj₂ le_rfl hL₂ hN₂).1 h0)
    have E := E4 (img e.ι₂ L) (img e.ι₂ N) hs' hnc'
    rw [e.img_eq hAT, hRF₂, ← img_inf e.inj₂, relIndex_img e.inj₂ hB₂ hA₂,
      ← img_secFix e.inj₂ hA₂ hN₂ hL₂,
      relIndex_img e.inj₂ ((secFix_le A N L).trans hN₂) hN₂] at E
    exact E
  · rw [hU, e.img_eq hAT, hRF₂, ← img_inf e.inj₂, ← img_inf_centralizer e.inj₂ hU₂ hA₂,
      ← img_inf_centralizer e.inj₂ hU₂ hB₂] at E5
    exact (img_inj e.inj₂ hUA₂ (inf_le_left.trans hU₂)).1 E5

theorem d15_general [hf₁ : Finite G₁] [Finite G₂] (h : D11Hyp G₁ G₂ T V M₂) :
    ¬ V ≤ pCoreOf 2 G₂ ∨
    (qSub G₁ V hf₁ h.reduced.1 h.reduced.2.2.1 ≤ 1 ∧ IsFFInt G₁ V h.reduced.2.2.1) ∨
    IsDualFFInt G₁ V h.reduced.2.2.1 ∨
    (qSub G₁ V hf₁ h.reduced.1 h.reduced.2.2.1 ≤ 2 ∧
      (∀ x ∈ conjClosure V G₂, ∀ y ∈ conjClosure V G₂, x * y = y * x) ∧
      ∃ c : ℕ, 2 ≤ c ∧ IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) c) ∨
    (((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).subgroupOf G₂).Normal ∧
      IsElemAbelian 2 (conjClosure V G₂) ∧
      IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1 ∧
      ⁅conjClosure V G₂, twoResidual G₂⁆ ≤ centerOf (pCoreOf 2 G₂) ∧
      twoResidual G₂ = ⁅twoResidual G₂, thompsonJ (pCoreOf 2 G₁)⁆ ∧
      thompsonJ (pCoreOf 2 G₁) = thompsonJ T) := by
  obtain ⟨F, _, _, ⟨e⟩⟩ := exists_emb (T := T) h.sylow₁.1 h.sylow₂.1
  have h' := d11Hyp_img e h
  have hc := inputD15_holds F _ _ _ _ _ h'
  unfold EmptyFaithfulMultiple.D15ConclAS at hc
  have hV₁ : V ≤ G₁ := h.reduced.1
  have hVT : V ≤ T := h.V_le_T
  have hV₂ : V ≤ G₂ := hVT.trans e.le₂
  have hR₁ : pCoreOf 2 G₁ ≤ G₁ := CFSG.LieType.BorelTits.pCoreOf_le 2 G₁
  have hR₂ : pCoreOf 2 G₂ ≤ G₂ := CFSG.LieType.BorelTits.pCoreOf_le 2 G₂
  have hRT : pCoreOf 2 G₁ ≤ T := h.pCoreOf_le_T
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
  have hq : qInt (img e.ι₁ G₁) (img e.ι₁ V) h'.reduced.2.2.1 =
      qSub G₁ V hf₁ h.reduced.1 h.reduced.2.2.1 :=
    qInt_img e.inj₁ le_rfl hV₁ hf₁ h.reduced.2.2.1 h'.reduced.2.2.1
  have hff : IsFFInt (img e.ι₁ G₁) (img e.ι₁ V) h'.reduced.2.2.1 ↔
      IsFFInt G₁ V h.reduced.2.2.1 :=
    isFFInt_img_iff e.inj₁ le_rfl hV₁ h.reduced.2.2.1 h'.reduced.2.2.1
  have hdual : IsDualFFInt (img e.ι₁ G₁) (img e.ι₁ V) h'.reduced.2.2.1 ↔
      IsDualFFInt G₁ V h.reduced.2.2.1 :=
    isDualFFInt_img_iff e.inj₁ le_rfl hV₁ h.reduced.2.2.1 h'.reduced.2.2.1
  rcases hc with h1 | h2 | h3 | h4 | h5
  ·
    refine Or.inl fun hle => h1 ?_
    rw [hVeq, hRF₂]
    exact img_mono hle
  ·
    rw [hq, hff] at h2
    exact Or.inr (Or.inl h2)
  ·
    exact Or.inr (Or.inr (Or.inl (hdual.1 h3)))
  ·
    obtain ⟨hq2, hab, c, hc2, hser⟩ := h4
    rw [hq] at hq2
    rw [hU] at hab hser
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hq2, (comm_img_iff e.inj₂ hU₂).1 hab, c, hc2,
      (isChiefSeriesFrom_img_iff e.inj₂ le_rfl hU₂ hU₂ c).1 hser⟩)))
  ·
    obtain ⟨hn, hea, hser, hcom, hres, hJ⟩ := h5
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩)))
    · rw [hRF₁, hReq, hRF₂, ← img_inf e.inj₂] at hn
      exact (normal_img_iff e.inj₂ (inf_le_right.trans hR₂) le_rfl).1 hn
    · rw [hU] at hea
      exact (isElemAbelian_img_iff e.inj₂ hU₂ 2).1 hea
    · rw [hU] at hser
      exact (isChiefSeriesFrom_img_iff e.inj₂ le_rfl hU₂ hU₂ 1).1 hser
    · rw [hU, hRF₂, ← img_twoResidual e.inj₂ le_rfl, ← img_centerOf e.inj₂ hR₂,
        ← img_commutator hU₂ hO₂] at hcom
      exact (img_le_img_iff e.inj₂ (commutator_le_of_le hU₂ hO₂)).1 hcom
    · rw [hRF₁, hReq, ← img_thompsonJ e.inj₂ (hRT.trans e.le₂),
        ← img_twoResidual e.inj₂ le_rfl, ← img_commutator hO₂ ((hJR.trans hRT).trans e.le₂)] at hres
      exact (img_inj e.inj₂ hO₂ (commutator_le_of_le hO₂ ((hJR.trans hRT).trans e.le₂))).1 hres
    · rw [hRF₁, ← img_thompsonJ e.inj₁ hR₁, ← img_thompsonJ e.inj₁ e.le₁] at hJ
      exact (img_inj e.inj₁ (hJR.trans hR₁) (hJT.trans e.le₁)).1 hJ

end CFSG.Quasithin.MS09

end
