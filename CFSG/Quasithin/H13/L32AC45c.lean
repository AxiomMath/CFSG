module

public import CFSG.Quasithin.H13.L32AC45b
public import CFSG.Quasithin.H13.L32ACSk6
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4IsPSL
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem card_of_alt7_or_hat {X : Type} [Group X]
    (h : IsAlt 7 X ∨ IsHat X ↥(alternatingGroup (Fin 7))) :
    Nat.card X = 2520 ∨ Nat.card X = 7560 := by
  have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [A7.card_alternating_fin 7 (by norm_num)]
    decide
  rcases h with ⟨⟨e⟩⟩ | ⟨-, hZ3, ⟨eZ⟩⟩
  · exact Or.inl (by rw [Nat.card_congr e.toEquiv, h7])
  · refine Or.inr ?_
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X),
      Nat.card_congr eZ.toEquiv, h7, hZ3]

theorem card_of_isPSL_three_two {X : Type} [Group X] (h : IsPSL 3 2 1 X) : Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

theorem card_of_isPSL_five_two {X : Type} [Group X] (h : IsPSL 5 2 1 X) :
    Nat.card X = 9999360 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two h

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem l1_le_of_stabilizesFive (S : Setting147 G T L V H) {K K₁ : Subgroup G}
    (hHG : H ≤ A6.g1 T V) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hKK₁ : K ≤ K₁) (hl1K₁ : l1 T L V ≤ K₁)
    (hB5 : IsAlt 5 ↥(modO2Image (A6.g1 T V) K))
    (hZL : Subgroup.center ↥(modO2Image (A6.g1 T V) K₁) = ⊥)
    (hst : StabilizesFivePoints (modO2Image (A6.g1 T V) K) (modO2Image (A6.g1 T V) K₁)) :
    l1 T L V ≤ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set G₁ := A6.g1 T V with hG₁
  set Q := ↥G₁ ⧸ CFSG.pCore 2 ↥G₁ with hQ
  set B := modO2Image G₁ K with hB
  set Lb := modO2Image G₁ K₁ with hLb
  have hBL : B ≤ Lb := Subgroup.map_mono fun _ hx => hKK₁ hx
  obtain ⟨f, hfr, hfk, S5, hS5, hN⟩ := hst
  have hf : Function.Injective f :=
    (MonoidHom.ker_eq_bot_iff f).mp (le_bot_iff.mp (hfk.trans hZL.le))
  have hTG : T ≤ G₁ := (le_sup_right.trans S.hz.1.1).trans hHG
  have hPT : pCoreOf 2 G₁ ≤ T := L32A.pCoreOf_le_of_le S.hyp hTG
  have hP2 : IsPGroup 2 (pCoreOf 2 G₁) := pCoreOf_isPGroup 2 G₁
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  have hxl1 : x ∈ l1 T L V := Subgroup.subset_closure hx
  have hxH : x ∈ H := (le_sup_left.trans S.hz.1.1) hxl1
  have hxG : x ∈ G₁ := hHG hxH
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hKn hxH
  set xb : Q := QuotientGroup.mk' (CFSG.pCore 2 ↥G₁) ⟨x, hxG⟩ with hxb
  have hxL : xb ∈ Lb := ⟨⟨x, hxG⟩, Subgroup.mem_subgroupOf.mpr (hl1K₁ hxl1), rfl⟩
  have hxB : xb ∈ Subgroup.normalizer (B : Set Q) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨x, hxG⟩ * a * ⟨x, hxG⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hxN _).mp (Subgroup.mem_subgroupOf.mp ha)
    · simp only [hxb, map_mul, map_inv]
  have hodd : Odd (orderOf (⟨xb, hxL⟩ : ↥Lb)) := by
    rw [Subgroup.orderOf_mk]
    refine Odd.of_dvd_nat hx.2 ?_
    have h1 := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥G₁)) (⟨x, hxG⟩ : ↥G₁)
    rwa [Subgroup.orderOf_mk] at h1
  have hxB' : xb ∈ B :=
    mem_of_stabilizesFive hBL (card_of_isAlt_five hB5) hf hfr hS5 hN hxB hodd
  obtain ⟨a, haK, hae⟩ := Subgroup.mem_map.mp hxB'
  rw [Subgroup.mem_subgroupOf] at haK
  rw [hxb, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hae
  have hq : (a : G)⁻¹ * x ∈ pCoreOf 2 G₁ := ⟨_, hae, rfl⟩
  have hxs : x ∈ K ⊔ pCoreOf 2 G₁ := by
    have e : x = (a : G) * ((a : G)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem_sup haK hq
  exact mem_of_odd_of_sup_pGroup hP2 (hPT.trans hTK) hxs hx.2

theorem lemma14_7_45_two_of
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    (h314 : A314Facts) (hF318 : A318Facts) (hD310 : D310) (hD391 : D391) (hI4 : Insp4)
    (hFine : F918Fine4) (h28 : Lemma14_7_28) (h30 : Lemma14_7_30) (h32 : Lemma14_7_32)
    (h736 : Lemma14_7_36) (h45 : Lemma14_7_45_A5) (S : Setting147 G T L V H) {K : Subgroup G}
    (hK : K ∈ cComp H) (hHeq : H = K ⊔ (l1 T L V ⊔ T)) {n : ℕ} (hn : 1 < n)
    (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K))) :
    K ∈ cComp (A6.g1 T V) ∨
      (l1 T L V ≤ K ∧ ∃ K₁ ∈ cComp (A6.g1 T V), K < K₁ ∧ IsAlt 7 (cStar K₁)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S₁ := setting_g1 h1332 h1334 S
  have hHG : H ≤ A6.g1 T V := S.hz.2.1
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hTG : T ≤ A6.g1 T V := hTH.trans hHG
  have hKH := le_of_mem_cComp hK
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := h32 G T L V H S K hK
  have hKn := le_normalizer_of_setting h37 h38 S hK hTK
  have hA5 : IsAlt 5 (cStar K) := h45 G T L V H S K hK hHeq n hn hLie
  have hTsyl : IsSylowTwoOf T (A6.g1 T V) :=
    isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTG
  have hKl : K ∈ lFamily T := cComp_subset_lFamily hTH hK
  obtain ⟨K₁, hK₁, hKK₁⟩ := CFSG.Quasithin.lemma_1_2_4_exists S.hyp.fsu.qtke S.hyp.fsu.simple
    S.hyp.fsu.nonabelian h37 h39 S₁.hz.1.2 hTsyl (hKH.trans hHG) hKl
  rcases eq_or_ne K K₁ with rfl | hne
  · exact Or.inl hK₁
  right
  have hlt : K < K₁ := lt_of_le_of_ne hKK₁ hne
  obtain ⟨hq₁, hTK₁, S₁', hF₁⟩ := reduce_KL1T h30 h32 S₁ hK₁
  have hK₁' : K₁ ∈ cComp (K₁ ⊔ (l1 T L V ⊔ T)) := hF₁.K_cComp
  have h60 : Nat.card (cStar K) = 60 := card_of_isAlt_five hA5
  have htrick : ∀ m : ℕ, 1 < m → A315.IsLieChar2 m (cStar K₁ ⧸ Subgroup.center (cStar K₁)) →
      False := fun m hm hLie₁ => by
    have hA := h45 G T L V _ S₁' K₁ hK₁' rfl m hm hLie₁
    exact hne (eq_of_card_cStar_eq S.hyp hTG hK₁ hKK₁ hTK
      (by rw [h60, card_of_isAlt_five hA])).symm
  have hL3 := relIndex_l1 h1222 h1332 h1334 S.hyp
  have hZ3 := card_center_cStar_dvd_three h28 S₁ hL3 hK₁
  have hz : Nat.card (Subgroup.center (cStar K₁)) = 1 ∨
      Nat.card (Subgroup.center (cStar K₁)) = 3 := (Nat.dvd_prime Nat.prime_three).1 hZ3
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (cStar K₁))
  have hdvd : 60 ∣ Nat.card (cStar K₁) := h60 ▸ (card_dvd_of_le hKK₁).1
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF₁
  have h4 := (F918_4_fine' hF₁ (sqtkGroup_of_setting S₁') (conjClosure_T_eq_self hTK₁) hV₁I hIU
    W hW hirrU hD310 hD391 hI4 hFine).1
  obtain ⟨eA⟩ := L1295B.nonempty_mulEquiv_autIH hF₁
  obtain ⟨hlist, h7⟩ := fourList_of_mulEquiv ((cStarEquiv K₁).trans eA) h4
  have hG₁K₁ := le_normalizer_of_setting h37 h38 S₁ hK₁ hTK₁
  have hres := fun hl => a314_two_of_list h36 h312 h314 (sqtkGroup_of_setting S₁) hTsyl
    (hKH.trans hHG) hKl hTK hA5 hK₁ hG₁K₁ hlt hq₁ hl
  have hnot7 : ∀ c : ℕ, Nat.card (cStar K₁ ⧸ Subgroup.center (cStar K₁)) = c →
      c = 360 ∨ c = 20160 ∨ c = 9999360 → A7.List1222 (cStar K₁) → False := by
    intro c hc hc' hl
    obtain ⟨⟨eL⟩, -, h7L, -⟩ := hres hl
    have h1 := card_of_alt7_or_hat h7L
    rw [← Nat.card_congr eL.toEquiv, hcard, hc] at h1
    rcases hz with hz | hz <;> rw [hz] at h1 <;> omega
  rcases hlist with ⟨m, hm, h | h | h⟩ | ⟨m, hm, h⟩ | ⟨m, hm, h⟩ | h | ⟨m, hm, h⟩ | h | h | h |
      h | h
  · exact (htrick m (by omega) (Or.inl h)).elim
  · exact (htrick m (by omega) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h)))))))).elim
  · exact (htrick m (by omega) (Or.inr (Or.inr (Or.inl h)))).elim
  ·
    rcases Nat.lt_or_ge 1 m with hm1 | hm1
    · exact (htrick m hm1 (Or.inr (Or.inl h))).elim
    · obtain rfl : m = 1 := le_antisymm hm1 hm
      rw [hcard, card_of_isPSL_three_two h] at hdvd
      exfalso
      rcases hz with hz | hz <;> rw [hz] at hdvd <;> omega
  · exact (htrick m (by omega) (Or.inr (Or.inr (Or.inr (Or.inl h))))).elim
  ·
    obtain ⟨e6⟩ := h
    have hc6 : Nat.card (cStar K₁ ⧸ Subgroup.center (cStar K₁)) = 360 := by
      rw [Nat.card_congr e6.toEquiv, A7.card_alternating_fin 6 (by norm_num)]
      decide
    exact (hnot7 360 hc6 (Or.inl rfl) (list1222_of_quot (by norm_num) (by norm_num) e6)).elim
  · exact (htrick m (by omega) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))).elim
  ·
    rw [hcard, SBc11.card_of_isPSU_three_three h] at hdvd
    exfalso
    rcases hz with hz | hz <;> rw [hz] at hdvd <;> omega
  ·
    obtain ⟨e8⟩ := CFSG.Quasithin.J4L4.alt8_of_isPSL h
    have hc8 : Nat.card (cStar K₁ ⧸ Subgroup.center (cStar K₁)) = 20160 := by
      rw [Nat.card_congr e8.toEquiv, A7.card_alternating_fin 8 (by norm_num)]
      decide
    exact (hnot7 20160 hc8 (Or.inr (Or.inl rfl))
      (list1222_of_quot (by norm_num) (by norm_num) e8)).elim
  ·
    have hZb := center_eq_bot_of_psl_two hq₁.1 h (odd_card_center_cStar K₁)
    have hc5 := card_of_isPSL_five_two h
    have hl : A7.List1222 (cStar K₁) := by
      refine Or.inl (Or.inr (Or.inr ?_))
      rw [hcard, hc5, hZb, Subgroup.card_bot, mul_one]
    exact (hnot7 9999360 hc5 (Or.inr (Or.inr rfl)) hl).elim
  ·
    have hZb : Subgroup.center (cStar K₁) = ⊥ := by
      rcases hz with hz | hz
      · exact Subgroup.card_eq_one.mp hz
      · exact absurd ⟨hq₁, hz, h⟩ (h7 h)
    obtain ⟨e7⟩ := h
    have hA7 : IsAlt 7 (cStar K₁) :=
      ⟨((QuotientGroup.quotientMulEquivOfEq hZb).trans QuotientGroup.quotientBot).symm.trans e7⟩
    obtain ⟨⟨eL⟩, hB5, -, hst⟩ := hres (list1222_of_quot (by norm_num) (by norm_num) e7)
    have hZL : Subgroup.center ↥(modO2Image (A6.g1 T V) K₁) = ⊥ := by
      apply Subgroup.card_eq_one.mp
      rw [← card_center_eq_of_mulEquiv eL, hZb, Subgroup.card_bot]
    have hl1K₁ : l1 T L V ≤ K₁ := by
      have hQ' : CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv (cStarEquiv K₁) hq₁
      obtain ⟨eA7⟩ := hA7
      have hKeq := eq_oPrimeResidualOf_three_of_exclusion hF318 h36 h38
        (sqtkGroup_of_setting S₁') hK₁' hQ' ((cStarEquiv K₁).symm.trans eA7)
        a318Exclusion_alt7
      rw [hKeq]
      exact oTwoUpper_le_oPrimeResidualOf_three hL3 (le_sup_left.trans le_sup_right)
    exact ⟨l1_le_of_stabilizesFive S hHG hTK hKn hKK₁ hl1K₁ hB5 hZL hst, K₁, hK₁, hlt, hA7⟩
  ·
    exact (h736 G T L V _ S₁ K₁ hK₁ .M22 h).elim

end CFSG.Quasithin.H13.L32A.C
