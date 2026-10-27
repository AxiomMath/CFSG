module

public import CFSG.Quasithin.Background.SimsD1Three
public import CFSG.Quasithin.Background.SimsD1Transport

public section

namespace CFSG.Quasithin.SimsD1.ThreeGen

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.SimsD1.Transport

section Helpers

variable {G : Type} [Group G]

theorem twoPrimeResidual_le_self (X : Subgroup G) : twoPrimeResidual X ≤ X :=
  iInf₂_le X ⟨le_rfl, Subgroup.le_normalizer, by rw [Subgroup.relIndex_self]; decide⟩

theorem map_conj_le {X H : Subgroup G} (hX : X ≤ H) {g : G} (hg : g ∈ H) :
    X.map (MulAut.conj g⁻¹).toMonoidHom ≤ H := by
  rintro _ ⟨x, hx, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  exact H.mul_mem (H.mul_mem (H.inv_mem hg) (hX hx)) hg

theorem secFix_le (X N L : Subgroup G) : Three.secFix X N L ≤ N := fun _ hx => hx.1

theorem secFix_map_eq {A B : Type} [Group A] [Group B] (f : A →* B) (hf : Function.Injective f)
    (X N L : Subgroup A) :
    Three.secFix (X.map f) (N.map f) (L.map f) = (Three.secFix X N L).map f := by
  ext y
  constructor
  · rintro ⟨⟨x, hxN, rfl⟩, hyL, hy⟩
    refine ⟨x, ⟨hxN, (TransGrp.mem_normalizer_map_iff f hf L x).1 hyL, fun a ha => ?_⟩, rfl⟩
    have h1 := hy (f a) ⟨a, ha, rfl⟩
    simp only [← map_inv, ← map_mul] at h1
    exact (Subgroup.mem_map_iff_mem hf).1 h1
  · rintro ⟨x, ⟨hxN, hxL, hx⟩, rfl⟩
    refine ⟨⟨x, hxN, rfl⟩, (TransGrp.mem_normalizer_map_iff f hf L x).2 hxL, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    simp only [← map_inv, ← map_mul]
    exact ⟨_, hx a ha, rfl⟩

variable {F : Type} [Group F] {H : Subgroup G} {ι : ↥H →* F}

theorem img_secFix (hι : Function.Injective ι) {X N L : Subgroup G} (hX : X ≤ H) (hN : N ≤ H)
    (hL : L ≤ H) : img ι (Three.secFix X N L) = Three.secFix (img ι X) (img ι N) (img ι L) := by
  obtain ⟨X, rfl⟩ := exists_map_subtype hX
  obtain ⟨N, rfl⟩ := exists_map_subtype hN
  obtain ⟨L, rfl⟩ := exists_map_subtype hL
  rw [secFix_map_eq _ H.subtype_injective]
  simp only [img_map_subtype]
  exact (secFix_map_eq ι hι X N L).symm

theorem img_conj' {X : Subgroup G} (hX : X ≤ H) {g : G} (hg : g ∈ H) :
    img ι (X.map (MulAut.conj g⁻¹).toMonoidHom) =
      (img ι X).map (MulAut.conj (ι ⟨g, hg⟩)⁻¹).toMonoidHom :=
  img_conj hX ⟨g, hg⟩

theorem quad_img_iff (hι : Function.Injective ι) {U A : Subgroup G} (hU : U ≤ H) (hA : A ≤ H) :
    (⁅⁅img ι U, img ι A⁆, img ι A⁆ = ⊥ ∧ ⁅img ι U, img ι A⁆ ≠ ⊥) ↔
      (⁅⁅U, A⁆, A⁆ = ⊥ ∧ ⁅U, A⁆ ≠ ⊥) := by
  have hUA : ⁅U, A⁆ ≤ H := commutator_le_of_le hU hA
  rw [← img_commutator hU hA, ← img_commutator hUA hA, ne_eq, ne_eq,
    img_eq_bot_iff hι (commutator_le_of_le hUA hA), img_eq_bot_iff hι hUA]

end Helpers

variable {G : Type} [Group G] {G₁ G₂ T V M₂ : Subgroup G}

theorem d13_general (hN : D125NonsolvableSQTK) [hf₁ : Finite G₁] [Finite G₂]
    (h : D11Hyp G₁ G₂ T V M₂)
    (hq : (1 : WithTop ℚ) < qSub G₁ V hf₁ h.reduced.1 h.reduced.2.2.1)
    (hVR₂ : V ≤ pCoreOf 2 G₂) (c : ℕ) (hc : 2 ≤ c)
    (hser : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) c) :
    IsElemAbelian 2 (conjClosure V G₂) ∧
    pCoreOf 2 G₂ ⊓ Subgroup.centralizer (conjClosure V G₂ : Set G) =
      twoPrimeResidual (G₂ ⊓ Subgroup.centralizer (conjClosure V G₂ : Set G)) ∧
    (CFSG.SectionRank.IsSQTKCat ↥G₂ → qSub G₁ V hf₁ h.reduced.1 h.reduced.2.2.1 ≤ 2) ∧
    ((∀ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2 G₁) A ↔ IsMaxElemAbelian T A) ∧
      (∃ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2 G₁) A ∧
        ⁅⁅conjClosure V G₂, A⁆, A⁆ = ⊥ ∧ ⁅conjClosure V G₂, A⁆ ≠ ⊥) ∧
      (∀ A : Subgroup G, (IsMaxElemAbelian (pCoreOf 2 G₁) A ∧ ¬ A ≤ pCoreOf 2 G₂ ∧
          ∀ A' : Subgroup G, IsMaxElemAbelian (pCoreOf 2 G₁) A' → ¬ A' ≤ pCoreOf 2 G₂ →
            A' ⊔ pCoreOf 2 G₂ ≤ A ⊔ pCoreOf 2 G₂ → A' ⊔ pCoreOf 2 G₂ = A ⊔ pCoreOf 2 G₂) →
        ∃ A' : Subgroup G, IsMaxElemAbelian (pCoreOf 2 G₁) A' ∧
          A' ⊔ pCoreOf 2 G₂ = A ⊔ pCoreOf 2 G₂ ∧ A' ≤ A ⊔ conjClosure V G₂ ∧
          (⁅⁅conjClosure V G₂, A'⁆, A'⁆ = ⊥ ∧ ⁅conjClosure V G₂, A'⁆ ≠ ⊥))) ∧
    (CFSG.SectionRank.IsSQTKCat ↥G₂ → qSub G₁ V hf₁ h.reduced.1 h.reduced.2.2.1 = 2 →
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
              padicValNat 2 ((Three.secFix A N L).relIndex N)) ∧
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
  obtain ⟨hF1, hF2, hF3, ⟨hF4a, hF4b, hF4c⟩, hF5⟩ := Three.d13_finite hN h' hnff' hVR₂' hc hser'
  have hmaxR : ∀ A : Subgroup G, A ≤ pCoreOf 2 G₁ →
      (IsMaxElemAbelian (pCoreOf 2 (img e.ι₁ G₁)) (img e.ι₁ A) ↔
        IsMaxElemAbelian (pCoreOf 2 G₁) A) := fun A hA => by
    rw [hRF₁]
    exact isMaxElemAbelian_img_iff e.inj₁ hR₁ (hA.trans hR₁)
  have hpull : ∀ A : Subgroup F, IsMaxElemAbelian (pCoreOf 2 (img e.ι₁ G₁)) A →
      ∃ A₀ : Subgroup G, A₀ ≤ pCoreOf 2 G₁ ∧ img e.ι₁ A₀ = A := fun A hA => by
    rw [hRF₁] at hA
    exact exists_img_of_le e.inj₁ hR₁ hA.1
  refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  ·
    rw [hU] at hF1
    exact (isElemAbelian_img_iff e.inj₂ hU₂ 2).1 hF1
  ·
    rw [hRF₂, hU, ← img_inf_centralizer e.inj₂ hR₂ hU₂, ← img_inf_centralizer e.inj₂ le_rfl hU₂,
      ← img_twoPrimeResidual e.inj₂ inf_le_left] at hF2
    exact (img_inj e.inj₂ (inf_le_left.trans hR₂)
      ((twoPrimeResidual_le_self _).trans inf_le_left)).1 hF2
  ·
    intro hsq
    rw [← hq']
    exact hF3 ((isSQTKCat_img_iff e.inj₂ le_rfl).2 hsq)
  ·
    intro A
    by_cases hAT : A ≤ T
    · have h1 := hF4a (img e.ι₁ A)
      rw [hRF₁, isMaxElemAbelian_img_iff e.inj₁ hR₁ (hAT.trans e.le₁),
        isMaxElemAbelian_img_iff e.inj₁ e.le₁ (hAT.trans e.le₁)] at h1
      exact h1
    · exact ⟨fun hA => absurd (hA.1.trans hRT) hAT, fun hA => absurd hA.1 hAT⟩
  ·
    obtain ⟨A₁, hA₁, hquad⟩ := hF4b
    obtain ⟨A, hAR, rfl⟩ := hpull A₁ hA₁
    have hAT : A ≤ T := hAR.trans hRT
    refine ⟨A, (hmaxR A hAR).1 hA₁, ?_⟩
    rw [hU, e.img_eq hAT] at hquad
    exact (quad_img_iff e.inj₂ hU₂ (hAT.trans e.le₂)).1 hquad
  ·
    rintro A ⟨hA, hAR₂, hAmin⟩
    have hAR : A ≤ pCoreOf 2 G₁ := hA.1
    have hAT : A ≤ T := hAR.trans hRT
    have hA₂ : A ≤ G₂ := hAT.trans e.le₂
    have hnot : ¬ img e.ι₁ A ≤ pCoreOf 2 (img e.ι₂ G₂) := by
      rw [hRF₂, e.img_eq hAT]
      exact fun hle => hAR₂ ((img_le_img_iff e.inj₂ hA₂).1 hle)
    have hminF : ∀ A₁ : Subgroup F, IsMaxElemAbelian (pCoreOf 2 (img e.ι₁ G₁)) A₁ →
        ¬ A₁ ≤ pCoreOf 2 (img e.ι₂ G₂) →
        A₁ ⊔ pCoreOf 2 (img e.ι₂ G₂) ≤ img e.ι₁ A ⊔ pCoreOf 2 (img e.ι₂ G₂) →
        A₁ ⊔ pCoreOf 2 (img e.ι₂ G₂) = img e.ι₁ A ⊔ pCoreOf 2 (img e.ι₂ G₂) := by
      intro A₁ hA₁ hnA₁ hle
      obtain ⟨A', hA'R, rfl⟩ := hpull A₁ hA₁
      have hA'T : A' ≤ T := hA'R.trans hRT
      have hA'₂ : A' ≤ G₂ := hA'T.trans e.le₂
      rw [hRF₂, e.img_eq hA'T] at hnA₁
      rw [hRF₂, e.img_eq hA'T, e.img_eq hAT, ← img_sup hA'₂ hR₂, ← img_sup hA₂ hR₂] at hle ⊢
      rw [hAmin A' ((hmaxR A' hA'R).1 hA₁) (fun h0 => hnA₁ (img_mono h0))
        ((img_le_img_iff e.inj₂ (sup_le hA'₂ hR₂)).1 hle)]
    obtain ⟨A₁, hA₁, hsup, hle, hquad⟩ := hF4c (img e.ι₁ A) ⟨(hmaxR A hAR).2 hA, hnot, hminF⟩
    obtain ⟨A'', hA''R, rfl⟩ := hpull A₁ hA₁
    have hA''T : A'' ≤ T := hA''R.trans hRT
    have hA''₂ : A'' ≤ G₂ := hA''T.trans e.le₂
    refine ⟨A'', (hmaxR A'' hA''R).1 hA₁, ?_, ?_, ?_⟩
    · rw [hRF₂, e.img_eq hA''T, e.img_eq hAT, ← img_sup hA''₂ hR₂, ← img_sup hA₂ hR₂] at hsup
      exact (img_inj e.inj₂ (sup_le hA''₂ hR₂) (sup_le hA₂ hR₂)).1 hsup
    · rw [hU, e.img_eq hA''T, e.img_eq hAT, ← img_sup hA₂ hU₂] at hle
      exact (img_le_img_iff e.inj₂ hA''₂).1 hle
    · rw [hU, e.img_eq hA''T] at hquad
      exact (quad_img_iff e.inj₂ hU₂ hA''₂).1 hquad
  ·
    intro hsq hq2
    obtain ⟨hc2, hall⟩ := hF5 ((isSQTKCat_img_iff e.inj₂ le_rfl).2 hsq) (hq'.trans hq2)
    refine ⟨hc2, fun A hA hAq => ?_⟩
    have hAR : A ≤ pCoreOf 2 G₁ := hA.1
    have hAT : A ≤ T := hAR.trans hRT
    have hA₂ : A ≤ G₂ := hAT.trans e.le₂
    have hB₂ : A ⊓ pCoreOf 2 G₂ ≤ G₂ := inf_le_right.trans hR₂
    have hUA₂ : conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G) ≤ G₂ := inf_le_left.trans hU₂
    have hquadF : ⁅⁅conjClosure (img e.ι₁ V) (img e.ι₂ G₂), img e.ι₁ A⁆, img e.ι₁ A⁆ = ⊥ ∧
        ⁅conjClosure (img e.ι₁ V) (img e.ι₂ G₂), img e.ι₁ A⁆ ≠ ⊥ := by
      rw [hU, e.img_eq hAT]
      exact (quad_img_iff e.inj₂ hU₂ hA₂).2 hAq
    obtain ⟨E1, E2, E3, E4, E5⟩ := hall (img e.ι₁ A) ((hmaxR A hAR).2 hA) hquadF
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

end CFSG.Quasithin.SimsD1.ThreeGen
