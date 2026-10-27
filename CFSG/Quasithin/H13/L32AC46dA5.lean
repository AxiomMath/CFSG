module

public import CFSG.Quasithin.H13.L32AC46d
public import CFSG.Quasithin.H13.L32AC46cA5
public import CFSG.Quasithin.H13.L32AC45c

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem lemma14_7_46_of_A5
    (hA5 : CFSG.Quasithin.F112R.F112SliceA5) (h4 : Lemma14_7_4_two_three) (hN1 : LieSylowOver3)
    (h29 : Thm14_7_29) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h312 : A312ForSQTK) (h314 : A314Facts) (hF318 : A318Facts) (hD310 : D310) (hD391 : D391)
    (hI4 : Insp4) (hFine : F918Fine4) (h28 : Lemma14_7_28) (h30 : Lemma14_7_30)
    (h32 : Lemma14_7_32) (h736 : Lemma14_7_36) (h45 : Lemma14_7_45_A5)
    (h1434 : Lemma1434One) : Lemma14_7_46 := by
  intro G _ _ T L V H S K hK hHeq n hn hLie
  by_contra hl1K
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hTG₁ : T ≤ A6.g1 T V := hTH.trans S.hz.2.1
  have hKH := le_of_mem_cComp hK
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := h32 G T L V H S K hK
  have hKl : K ∈ lFamily T := cComp_subset_lFamily hTH hK
  have hKG₁ : K ∈ cComp (A6.g1 T V) := by
    rcases lemma14_7_45_two_of h1222 h1332 h1334 h36 h37 h38 h39 h312 h314 hF318 hD310 hD391
      hI4 hFine h28 h30 h32 h736 h45 S hK hHeq hn hLie with h | ⟨h, -⟩
    · exact h
    · exact absurd h hl1K
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have hG₀ := lemma14_7_46_amalgam_of_A5 hA5 h4 hN1 h29 h1222 h1332 h1334 h37 h38 h30 h32 h45 G T
    L V H S K hK hHeq n hn hLie hl1K V₂ hV2
  set I₂ := L32A.i2 T V V₂ with hI₂
  set G₀ := I₂ ⊔ K ⊔ T with hG₀def
  have hTG₀ : T ≤ G₀ := le_sup_right
  have hKG₀ : K ≤ G₀ := le_sup_right.trans le_sup_left
  have hTsyl₀ : IsSylowTwoOf T G₀ := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTG₀
  obtain ⟨K₀, hK₀, hKK₀⟩ := CFSG.Quasithin.lemma_1_2_4_exists S.hyp.fsu.qtke S.hyp.fsu.simple
    S.hyp.fsu.nonabelian h37 h39 hG₀ hTsyl₀ hKG₀ hKl
  obtain ⟨-, hKL, -, hF918⟩ := h30 G T L V H S K hK
  have hKn := le_normalizer_of_setting h37 h38 S hK hTK
  have hHeq' : conjClosure K T ⊔ (l1 T L V ⊔ T) = H := by
    rw [conjClosure_T_eq_self hTK]
    exact hHeq.symm
  rw [hHeq'] at hF918
  have hF := hF918.toHypF98
  have hA5 := h45 G T L V H S K hK hHeq n hn hLie
  have h60 : Nat.card (cStar K) = 60 := card_of_isAlt_five hA5
  have hO2K : pCoreOf 2 K ≠ ⊥ := by
    intro hbot
    have h16 := sixteen_le_card_commutator hK hF hA5
    have hle := commutator_le_pCoreOf hKH hKn hF
    rw [hbot, le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at h16
    omega
  rcases eq_or_ne K K₀ with rfl | hne
  ·
    have hG₀K : G₀ ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKG₀).mp
        (lemma_1_2_4_normal S.hyp.fsu.qtke S.hyp.fsu.simple S.hyp.fsu.nonabelian h37 h38 hG₀
          hTsyl₀ (cComp_subset_lFamily hTG₀ hK₀) le_rfl hK₀ hTK)
    have hG₁K : A6.g1 T V ≤ Subgroup.normalizer (K : Set G) :=
      le_normalizer_of_setting h37 h38 (setting_g1 h1332 h1334 S) hKG₁ hTK
    have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
    obtain ⟨-, hI₂eq, -, -, -⟩ := h4 G T L V V₂ S.hyp hV2
    have hL₂I₂ : L₁Of L V₂ ≤ I₂ := by
      rw [hI₂, hI₂eq]
      exact le_sup_left
    have hLK : L ≤ Subgroup.normalizer (K : Set G) := S14.genL.trans
      (sup_le hG₁K (hL₂I₂.trans ((le_sup_left.trans le_sup_left).trans hG₀K)))
    have hXK : K ⊔ (L ⊔ T) ≤ Subgroup.normalizer (K : Set G) :=
      sup_le Subgroup.le_normalizer (sup_le hLK hTK)
    have hOX : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ (L ⊔ T)) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left)
        (hXK.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
    have hX := le_normalizer_L_of h1332 S.hyp (le_sup_right : L ⊔ T ≤ K ⊔ (L ⊔ T))
      fun h => hO2K (le_bot_iff.mp (h ▸ hOX))
    exact hKL (le_sup_left.trans hX)
  ·
    have hlt : K < K₀ := lt_of_le_of_ne hKK₀ hne
    have hK₀G₁ : ¬ K₀ ≤ A6.g1 T V := by
      intro hle
      have S₁ := setting_g1 h1332 h1334 S
      have hTsyl₁ : IsSylowTwoOf T (A6.g1 T V) :=
        isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTG₁
      obtain ⟨K₁, hK₁, hK₀K₁⟩ := CFSG.Quasithin.lemma_1_2_4_exists S.hyp.fsu.qtke
        S.hyp.fsu.simple S.hyp.fsu.nonabelian h37 h39 S₁.hz.1.2 hTsyl₁ hle
        (cComp_subset_lFamily hTG₀ hK₀)
      have huniq := lemma_1_2_4_existsUnique S.hyp.fsu.qtke S.hyp.fsu.simple
        S.hyp.fsu.nonabelian h37 h39 S₁.hz.1.2 hTsyl₁ (le_of_mem_cComp hKG₁) hKl
      have hKK₁ : K = K₁ := huniq.unique ⟨hKG₁, le_rfl⟩ ⟨hK₁, hKK₀.trans hK₀K₁⟩
      exact hlt.not_ge (hK₀K₁.trans hKK₁.ge)
    have hinH : InH ((S.hyp.fsu.sylow.1.toSylow S.hyp.fsu.sylow.2 : Sylow 2 G) : Subgroup G) G₀ :=
      ⟨hTG₀, hG₀⟩
    have hK₀f : quasithinIsFaithfulLocal T K₀ := by
      have hch : CharTwo G₀ := charTwo_of_inH S.hyp.fsu.qtke.2.1 _ hinH
      have hred := C1GN.isTwoReducedIn_VZ hch hTsyl₀
      refine isFaithfulLocal_of_commutator_ne_bot S.hyp.fsu.qtke.2.1 _ hinH hK₀ hred ?_
      intro hc
      apply hK₀G₁
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
      have hV1Z : fsuV1 T V ≤ VZ T G₀ := inf_le_right.trans (le_conjClosure _ _)
      exact (hc.trans (Subgroup.centralizer_le hV1Z)).trans (Subgroup.centralizer_le_normalizer _)
    have hdvd : 60 ∣ Nat.card (cStar K₀) := h60 ▸ (card_dvd_of_le hKK₀).1
    rcases h1434 G T L S.hyp.hyp K₀ hK₀f with ⟨⟨e⟩⟩ | hP
    · have hc : Nat.card (cStar K₀) = 60 := by
        rw [Nat.card_congr ((cStarEquiv K₀).trans e).toEquiv]
        exact card_of_isAlt_five ⟨MulEquiv.refl _⟩
      exact hne (eq_of_card_cStar_eq S.hyp hTG₀ hK₀ hKK₀ hTK (by rw [h60, hc])).symm
    · have hc : Nat.card (cStar K₀) = 168 := by
        rw [Nat.card_congr (cStarEquiv K₀).toEquiv]
        exact card_of_lieModel_psl_three_two hP
      rw [hc] at hdvd
      norm_num at hdvd

end CFSG.Quasithin.H13.L32A.C

end
