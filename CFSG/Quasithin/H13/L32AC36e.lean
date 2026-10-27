module

public import CFSG.Quasithin.H13.L32AC36d
public import CFSG.Quasithin.H13.L32AC47c
public import CFSG.Quasithin.H13.L32AC48b

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

attribute [local instance] commGroupOfFact

theorem mem_stabSub_of_eq_orbSup {W : Type} [CommGroup W] {T : Subgroup (MulAut W)}
    {U : Subgroup W} (h : U = orbSup T U) {t : MulAut W} (ht : t ∈ T) : t ∈ stabSub U := by
  have hmap : ∀ s ∈ T, ∀ u ∈ U, s u ∈ U := by
    intro s hs u hu
    rw [h]
    exact (le_iSup₂ (f := fun s (_ : s ∈ T) => U.map s.toMonoidHom) s hs) ⟨u, hu, rfl⟩
  intro u
  refine ⟨fun hu => ?_, hmap t ht u⟩
  have := hmap t⁻¹ (T.inv_mem ht) _ hu
  simpa using this

variable {G : Type} [Group G] [Finite G] {T L V H K : Subgroup G}

omit [Finite G] in
theorem isSimpleGroup_of_m22 (hM : IsSporadic .M22 (cStar K)) :
    IsSimpleGroup (cStar K) := by
  obtain ⟨eM⟩ := hM
  have := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have e' : cStar K ≃* ↥NativeSporadic.M22 := eM
  exact e'.isSimpleGroup

omit [Finite G] in
theorem card_of_m22 (hM : IsSporadic .M22 (cStar K)) :
    Nat.card (cStar K) = 443520 := by
  obtain ⟨eM⟩ := hM
  have e' : cStar K ≃* ↥NativeSporadic.M22 := eM
  rw [Nat.card_congr e'.toEquiv, CFSG.Sporadic.Mathieu.card_M22]

theorem card_autIH_m22 {I : Subgroup G}
    (hF : HypF918 T V L (fsuV1 T V) V H K) (hIU : I ≤ conjClosure V H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ fsuV1 T V)
    (hM : IsSporadic .M22 (cStar K)) : Nat.card ↥(autIH (fsuV1 T V) I H K) = 443520 := by
  have := factElem hF hIU
  have hS := isSimpleGroup_of_m22 hM
  have hS' : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := (cStarEquiv K).symm.isSimpleGroup
  have hne : autIH (fsuV1 T V) I H K ≠ ⊥ := by
    rw [autIH_eq_map hF (le_of_mem_cComp hF.K_cComp)]
    exact map_K_ne_bot hF hIU hnt
  obtain ⟨e⟩ := nonempty_mulEquiv_quotient_autI hF hIU hS' hne
  rw [← Nat.card_congr e.toEquiv, ← Nat.card_congr (cStarEquiv K).toEquiv]
  exact card_of_m22 hM

theorem exists_I_m22 (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h56 : AsB56) (hD310 : D310) (hD391 : D391) (hI4 : Insp4)
    (hFine : F918Fine4) (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hK₀ : conjClosure K T = K) (hHeq : H = conjClosure K T ⊔ T) (hl1K : l1 T L V ≤ K)
    (hM : IsSporadic .M22 (cStar K)) :
    ∃ I : Subgroup G, fsuV1 T V ≤ I ∧ ∃ hIU : I ≤ conjClosure V H,
      IsIrrPlusTildeT hF hIU ∧ H ≤ Subgroup.normalizer (I : Set G) ∧ V ≤ I := by
  have hSQ := sqtkGroup_of_setting S
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hTH : T ≤ H := hF.T_le_H
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have hirrT := isIrrPlusTildeT_of_ambient hF hIU W hW hirrU
  have hFct := factElem hF hIU
  have hirr' : subM (fsuV1 T V) (conjClosure I H) I ∈
      IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
        (orbSup (autIH (fsuV1 T V) I H T) (subM (fsuV1 T V) (conjClosure I H) I))
        (autIH (fsuV1 T V) I H T) := hirrT
  have hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G) :=
    K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have h4 := (F918_4_fine' hF hSQ hK₀ hV₁I hIU W hW hirrU hD310 hD391 hI4 hFine).2
  have hHI : H ≤ Subgroup.normalizer (I : Set G) := by
    rcases h4 with h4 | (⟨hVT, -⟩ | h3)
    · exact h4
    · have hTI : T ≤ Subgroup.normalizer (I : Set G) := by
        intro t ht
        have hst := mem_stabSub_of_eq_orbSup hVT (actH_mem_autIH_of_mem (I := I) hF hTH ht)
        exact (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁
          (hF.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H) hV₁I
          (le_conjClosure I H) ⟨t, hTH ht⟩).mp hst
      rw [hHeq]
      exact sup_le hKI hTI
    · exact (false_of_d310Two_card h3 (Or.inl (card_autIH_m22 hF hIU hnt hM))).elim
  have hcI : conjClosure I H = I :=
    le_antisymm (conjClosure_le fun _ hh i hi => (Subgroup.mem_normalizer_iff.mp (hHI hh) i).mp hi)
      (le_conjClosure I H)
  have hS' : IsSimpleGroup (KBar K) := isSimpleGroup_of_m22 hM
  have hZ : ∀ x ∈ conjClosure K T,
      (∀ k' ∈ conjClosure K T, x * k' * x⁻¹ * k'⁻¹ ∈ pCoreOf 2 H) → x ∈ pCoreOf 2 H := by
    rw [hK₀]
    exact hZ_comp hF.K_cComp hS'
  have hI := isIrrPlusTilde_of_module hF hV₁I hIU hirrT
  have hNo : HasNoFaithfulFFModulesMod (conjClosure K T ⊔ T) (pCoreOf 2 H) := by
    have hK' : K ∈ cComp (conjClosure K T ⊔ T) := hHeq ▸ hF.K_cComp
    have hKn : (K.subgroupOf (conjClosure K T ⊔ T)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hK'), ← hHeq]
      exact hK₀ ▸ hF.K₀_normal
    have hXeq : conjClosure K T ⊔ T = K ⊔ T := by rw [hK₀]
    have hsq : SQTKGroup ↥(conjClosure K T ⊔ T) := hHeq ▸ hSQ
    have h := noFaithfulFF_m22 h56 hK' hKn hXeq le_sup_right hF.sylow_H.2.1 hsq hM
    have hp : pCoreOf 2 (conjClosure K T ⊔ T) = pCoreOf 2 H := by rw [← hHeq]
    rw [hp] at h
    exact h
  have h7 := hF.F918_7' hHeq hZ hV₁I hIU hI hNo
  rw [hcI] at h7
  refine ⟨I, hV₁I, hIU, hirrT, hHI, fun v hv => ?_⟩
  have hVN : V ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (le_conjClosure V H).trans (hF.conjClosure_le_normalizer_V₁ (le_conjClosure V H))
  have hVc : V ≤ ⁅conjClosure V H, conjClosure K T⁆ :=
    (le_commutator_l1 h1222 h1332 h1334 S.hyp).trans
      (Subgroup.commutator_mono (le_conjClosure V H) (hl1K.trans (le_conjClosure K T)))
  have h1 : secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨v, hVN hv⟩ ∈
      tildeOf (fsuV1 T V) I := by
    rw [h7]
    exact secMk_mem_secImg (hVc hv)
  exact (secMk_mem_tildeOf_iff hV₁I).mp h1

end CFSG.Quasithin.H13.L32A.C
