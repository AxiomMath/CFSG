module

public import CFSG.Quasithin.Background.RonanH154Vocab
public import CFSG.Quasithin.Background.RonanH164Tconj

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH154

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143
  CFSG.Quasithin.RonanH163 CFSG.Quasithin.H.Mathieu

theorem xiV_map {V V' : Type*} [CommGroup V] [CommGroup V'] (e : V ≃* V')
    (G : Subgroup (MulAut V)) : xiV (G.map (cH e)) = (xiV G).map e.toMonoidHom := by
  unfold xiV
  simp only [Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun a' => iSup_le fun ha' => iSup_le fun ha'1 => ?_
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
    have hne : a ≠ 1 := fun h => ha'1 (by rw [h, map_one])
    refine le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le hne (le_of_eq ?_)))
    rw [← MonoidHom.map_zpowers (cH e) a, fixV_map]
  · refine iSup_le fun a => iSup_le fun ha => iSup_le fun hne => ?_
    have hne' : cH e a ≠ 1 := fun h => hne (cH_injective e (h.trans (map_one (cH e)).symm))
    refine le_iSup_of_le (cH e a) (le_iSup_of_le (Subgroup.mem_map_of_mem _ ha)
      (le_iSup_of_le hne' (le_of_eq ?_)))
    rw [← MonoidHom.map_zpowers (cH e) a, fixV_map]

theorem Concl154_map {V V' : Type*} [CommGroup V] [CommGroup V'] {Γ : Subgroup P24}
    (ρ : ↥Γ →* MulAut V) (ρ' : ↥Γ →* MulAut V') (e : V ≃* V')
    (he : ∀ (g : ↥Γ) (v : V), e (ρ g v) = ρ' g (e v)) (a b : Fin 24)
    (Q : Finset (Finset (Fin 24))) : Concl154 ρ a b Q → Concl154 ρ' a b Q := by
  unfold Concl154
  rintro ⟨⟨V₆, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, h11⟩, h3', h4'⟩
  have hM := rImg_map ρ ρ' e he (MY Γ Q)
  have hK := rImg_map ρ ρ' e he (KY Γ Q)
  have hI := rImg_map ρ ρ' e he (KY Γ Q ⊓ M22g a b)
  have hF : fixV (rImg ρ' (KY Γ Q)) = (fixV (rImg ρ (KY Γ Q))).map e.toMonoidHom := by
    rw [← hK, fixV_map]
  have hFI : fixV (rImg ρ' (KY Γ Q ⊓ M22g a b)) =
      (fixV (rImg ρ (KY Γ Q ⊓ M22g a b))).map e.toMonoidHom := by
    rw [← hI, fixV_map]
  have hT : (⊤ : Subgroup V).map e.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (e_toMonoidHom_surjective e)
  refine ⟨⟨V₆.map e.toMonoidHom, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · have h := (chief_map e (rImg ρ (MY Γ Q)) ⊥ (fixV (rImg ρ (KY Γ Q)))).mpr h1
    rw [Subgroup.map_bot, hM, ← hF] at h
    exact h
  · rw [hF, rk_map]
    exact h2
  · have h := (chief_map e (rImg ρ (MY Γ Q)) (fixV (rImg ρ (KY Γ Q)))
      (fixV (rImg ρ (KY Γ Q ⊓ M22g a b)))).mpr h3
    rw [hM, ← hF, ← hFI] at h
    exact h
  · rw [hFI, rk_map]
    exact h4
  · have h := (chief_map e (rImg ρ (MY Γ Q)) (fixV (rImg ρ (KY Γ Q ⊓ M22g a b))) V₆).mpr h5
    rw [hM, ← hFI] at h
    exact h
  · have h := (chief_map e (rImg ρ (MY Γ Q)) V₆ ⊤).mpr h6
    rw [hM, hT] at h
    exact h
  · exact (rk_map e V₆).trans h7
  · have h := (isDualOfConj_map ρ ρ' e he (MY Γ Q) V₆ (fixV (rImg ρ (KY Γ Q))) (KY Γ Q)).mpr h8
    rw [← hF] at h
    exact h
  · have h := (inducesOnSub_map e (rImg ρ (MY Γ Q)) ⊤ V₆ (G6.coreMod 5)
      (G6.permAct 5).range).mpr h9
    rw [hM, hT] at h
    exact h
  · intro g hg
    have key : ∀ x : V, e (ρ g x * x⁻¹) = ρ' g (e x) * (e x)⁻¹ := by
      intro x
      rw [map_mul, map_inv, he]
    have hv : (∀ x' : V', ρ' g x' * x'⁻¹ ∈ V₆.map e.toMonoidHom) ↔
        (∀ x : V, ρ g x * x⁻¹ ∈ V₆) := by
      constructor
      · intro h x
        have hx := h (e x)
        rw [← key x, mem_map_e_iff] at hx
        exact hx
      · intro h x'
        obtain ⟨x, rfl⟩ := e.surjective x'
        rw [← key x, mem_map_e_iff]
        exact h x
    exact hv.trans (h10 g hg)
  · have h := (fullTranspCenter_map e (rImg ρ (MY Γ Q)) (rImg ρ (KY Γ Q)) V₆
      (fixV (rImg ρ (KY Γ Q)))).mpr h11
    rw [hM, hK, ← hF] at h
    exact h
  · intro A hA hcard
    obtain ⟨hx, hr⟩ := h3' A hA hcard
    rw [← rImg_map ρ ρ' e he A]
    refine ⟨?_, ?_⟩
    · rw [xiV_map, hx, hT]
    · rw [fixV_map, rk_map]
      exact hr
  · have hFB : ∀ B : Subgroup P24, fixV (rImg ρ' B) = (fixV (rImg ρ B)).map e.toMonoidHom := by
      intro B
      rw [← rImg_map ρ ρ' e he B, fixV_map]
    have hS : (⨆ (B' : Subgroup P24) (_ : B' ≤ KY Γ Q) (_ : IsE2k 2 B'), fixV (rImg ρ' B')) =
        (⨆ (B' : Subgroup P24) (_ : B' ≤ KY Γ Q) (_ : IsE2k 2 B'), fixV (rImg ρ B')).map
          e.toMonoidHom := by
      simp only [Subgroup.map_iSup, hFB]
    rw [hS, h4', hT]

theorem Concl154_iff_of_iso {V V' : Type*} [CommGroup V] [CommGroup V'] {Γ : Subgroup P24}
    (ρ : ↥Γ →* MulAut V) (ρ' : ↥Γ →* MulAut V') (e : V ≃* V')
    (he : ∀ (g : ↥Γ) (v : V), e (ρ g v) = ρ' g (e v)) (a b : Fin 24)
    (Q : Finset (Finset (Fin 24))) : Concl154 ρ a b Q ↔ Concl154 ρ' a b Q := by
  refine ⟨Concl154_map ρ ρ' e he a b Q, Concl154_map ρ' ρ e.symm ?_ a b Q⟩
  intro g v'
  have h := he g (e.symm v')
  rw [MulEquiv.apply_symm_apply] at h
  rw [← h, MulEquiv.symm_apply_apply]

theorem Concl154_comp {V : Type*} [CommGroup V] {Γ Γ' : Subgroup P24} (c : P24)
    (hc : c ∈ AutPerm) (hΓ : conjSubg c Γ = Γ') (ρ' : ↥Γ' →* MulAut V) (φ : ↥Γ →* ↥Γ')
    (hφ : ∀ g : ↥Γ, (φ g : P24) = c * g * c⁻¹) (a b : Fin 24)
    (Q : Finset (Finset (Fin 24))) :
    Concl154 ρ' (c a) (c b) (c • Q) → Concl154 (ρ'.comp φ) a b Q := by
  have hM : rImg ρ' (MY Γ' (c • Q)) = rImg (ρ'.comp φ) (MY Γ Q) := by
    rw [h164w_MY_comp hΓ Q, rImg_comp c hΓ ρ' φ hφ]
  have hK : rImg ρ' (KY Γ' (c • Q)) = rImg (ρ'.comp φ) (KY Γ Q) := by
    rw [h164w_KY_comp hΓ Q, rImg_comp c hΓ ρ' φ hφ]
  have hKI : rImg ρ' (KY Γ' (c • Q) ⊓ M22g (c a) (c b)) =
      rImg (ρ'.comp φ) (KY Γ Q ⊓ M22g a b) := by
    have hI : KY Γ' (c • Q) ⊓ M22g (c a) (c b) = conjSubg c (KY Γ Q ⊓ M22g a b) := by
      rw [conjSubg_inf, h164w_KY_comp hΓ Q, M22g_conj hc a b]
    rw [hI, rImg_comp c hΓ ρ' φ hφ]
  have hR : rImg ρ' (conjSubg c (KY Γ Q)) = rImg (ρ'.comp φ) (KY Γ Q) :=
    (rImg_comp c hΓ ρ' φ hφ (KY Γ Q)).symm
  unfold Concl154
  rintro ⟨⟨V₆, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, h11⟩, h3', h4'⟩
  refine ⟨⟨V₆, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · rw [hM, hK] at h1
    exact h1
  · rw [hK] at h2
    exact h2
  · rw [hM, hK, hKI] at h3
    exact h3
  · rw [hKI] at h4
    exact h4
  · rw [hM, hKI] at h5
    exact h5
  · rw [hM] at h6
    exact h6
  · exact h7
  · rw [h164w_MY_comp hΓ Q, h164w_KY_comp hΓ Q, hR] at h8
    exact isDualOfConj_comp c hΓ ρ' φ hφ (MY Γ Q) V₆ _ (KY Γ Q) h8
  · rw [hM] at h9
    exact h9
  · intro g hg
    have hφg : (φ g : P24) ∈ MY Γ' (c • Q) := by
      rw [h164w_MY_comp hΓ Q, hφ g]
      exact h164w_mem_conj hg
    have hφK : (φ g : P24) ∈ KY Γ' (c • Q) ↔ (g : P24) ∈ KY Γ Q := by
      rw [h164w_KY_comp hΓ Q, hφ g, mem_conjSubg_iff,
        show c⁻¹ * (c * (g : P24) * c⁻¹) * c = (g : P24) by group]
    have h := h10 (φ g) hφg
    rw [hφK] at h
    exact h
  · rw [hM, hK] at h11
    exact h11
  · intro A hA hcard
    have hA' : conjSubg c A ≤ KY Γ' (c • Q) := by
      rw [h164w_KY_comp hΓ Q]
      exact conjSubg_le_conjSubg_iff.2 hA
    have hcard' : Nat.card (conjSubg c A) * 2 = Nat.card (KY Γ' (c • Q)) := by
      rw [card_conjSubg, h164w_KY_comp hΓ Q, card_conjSubg]
      exact hcard
    rw [rImg_comp c hΓ ρ' φ hφ A]
    exact h3' (conjSubg c A) hA' hcard'
  · apply eq_top_iff.2
    refine le_trans (le_of_eq h4'.symm)
      (iSup_le fun B'' => iSup_le fun hB'' => iSup_le fun hE => ?_)
    have hB'KY : conjSubg c⁻¹ B'' ≤ KY Γ Q := by
      refine (conjSubg_le_conjSubg_iff (c := c)).1 ?_
      rw [conjSubg_inv_conjSubg, ← h164w_KY_comp hΓ Q]
      exact hB''
    have hB'E : IsE2k 2 (conjSubg c⁻¹ B'') := by
      refine (IsE2k_conjSubg_iff c 2 (conjSubg c⁻¹ B'')).1 ?_
      rw [conjSubg_inv_conjSubg]
      exact hE
    have hfix : fixV (rImg ρ' B'') = fixV (rImg (ρ'.comp φ) (conjSubg c⁻¹ B'')) := by
      rw [rImg_comp c hΓ ρ' φ hφ, conjSubg_inv_conjSubg]
    rw [hfix]
    exact le_iSup_of_le (conjSubg c⁻¹ B'') (le_iSup_of_le hB'KY (le_iSup_of_le hB'E le_rfl))

theorem Concl154_of_transport {V V' : Type*} [CommGroup V] [CommGroup V'] {Γ Γ' : Subgroup P24}
    (c : P24) (hc : c ∈ AutPerm) (hΓ : conjSubg c Γ = Γ')
    (ρ : ↥Γ →* MulAut V) (ρ' : ↥Γ' →* MulAut V') (φ : ↥Γ →* ↥Γ')
    (hφ : ∀ g : ↥Γ, (φ g : P24) = c * g * c⁻¹) (e : V ≃* V')
    (he : ∀ (g : ↥Γ) (v : V), e (ρ g v) = ρ' (φ g) (e v)) (a b : Fin 24)
    (Q : Finset (Finset (Fin 24))) :
    Concl154 ρ' (c a) (c b) (c • Q) → Concl154 ρ a b Q := by
  intro h
  exact (Concl154_iff_of_iso ρ (ρ'.comp φ) e he a b Q).2
    (Concl154_comp c hc hΓ ρ' φ hφ a b Q h)

end CFSG.Quasithin.RonanH154
