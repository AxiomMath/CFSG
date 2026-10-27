module

public import CFSG.Quasithin.Vol2.Ch11SecD553B
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Background.E3Prop
public import CFSG.Quasithin.Vol2.Ch11StatementsD

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem mQuot_eq_of_card {V U : Subgroup G} (hV : IsPGroup 2 V) (hUV : U ≤ V) {b c : ℕ}
    (hb : Nat.card V = 2 ^ b) (hc : Nat.card U = 2 ^ c) : E3.mQuot V U + c = b := by
  have h := E3.card_eq_two_pow_mul hV hUV
  rw [hb, hc, ← pow_add] at h
  exact (Nat.pow_right_injective (le_refl 2) h).symm

theorem card_V₂ (h1141 : Stmt11_4_1) (h : Hyp11 G T L I n) {V₁ V₂ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂) : Nat.card V₂ = 2 ^ (2 * n) := by
  obtain ⟨X, hX⟩ := exists_isCartanX h
  have hr := SecA.IsVi.relIndex_eq hV₂
  rw [(h1141 G T L I n V₁ X h hV₁ hX).1.1, Subgroup.relIndex_bot_left] at hr
  rw [hr, mul_comm]

theorem stmt11_5_3_two (hTwo : TwoPointsFact) (hCard : CardVFact) (h1102 : Stmt11_0_2)
    (h1003 : Stmt11_0_3) (h1141 : Stmt11_4_1) (h1142 : Stmt11_4_2) (h1151 : Stmt11_5_1)
    (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hK : KOf L V₁ V₁ = LOf L V₁) :
    (KindSL3 L (fsuV T I) n → ((2 * n : ℕ) : ℕ∞) ≤ E3.rParam (fsuV T I)) ∧
      (KindSp4 L (fsuV T I) n → ((3 * n : ℕ) : ℕ∞) ≤ E3.rParam (fsuV T I)) := by
  have hset := natSetting11_of h1102 h1141 h hV₁
  have hone := fun g (hg : g ∉ Subgroup.normalizer (fsuV T I : Set G)) =>
    stmt11_5_3_one hTwo h1102 h1003 h1141 h1142 h1151 h hV₁ hK hg
  refine ⟨fun hSL => rParam_ge_of_card (k := 2) hone (card_V₁ h1141 h hV₁) ?_
    (SecA.isPGroup_fsuV h), fun hSp => rParam_ge_of_card (k := 3) hone (card_V₁ h1141 h hV₁) ?_
    (SecA.isPGroup_fsuV h)⟩
  · rw [(hCard G T L I n hset).1 hSL]
  · rw [(hCard G T L I n hset).2 hSp]

theorem stmt11_5_3_three (hTwo : TwoPointsFact) (hCard : CardVFact) (hRank : RankV2Fact)
    (hComm : PointCommFact) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1003 : Stmt11_0_3)
    (h1110 : Stmt11_1_0) (h1122 : Stmt11_2_2) (h1125 : Stmt11_2_5) (h1141 : Stmt11_4_1)
    (h1142 : Stmt11_4_2) (h1143 : Stmt11_4_3) (h1144 : Stmt11_4_4) (h1151 : Stmt11_5_1)
    (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hK : KOf L V₁ V₁ = LOf L V₁) :
    ¬ IsMulCommutative ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) := by
  intro habel
  have hset := natSetting11_of h1102 h1141 h hV₁
  have hkind := h1151 G T L I n h
  have hn := h.one_lt
  obtain ⟨V₂, hV₂, -⟩ := (h1110 G T L I n h).1 2 (by norm_num) (by norm_num)
  have hone := fun g (hg : g ∉ Subgroup.normalizer (fsuV T I : Set G)) =>
    stmt11_5_3_one hTwo h1102 h1003 h1141 h1142 h1151 h hV₁ hK hg
  have hVel := SecA.isElemAbelian_fsuV h
  have hV2 := SecA.isPGroup_fsuV h
  have hV₂V := SecA.IsVi.le_fsuV hV₂
  have hq2 : ∀ b, Nat.card (fsuV T I) = 2 ^ b → E3.mQuot (fsuV T I) V₂ + 2 * n = b :=
    fun b hb => mQuot_eq_of_card hV2 hV₂V hb (card_V₂ h1141 h hV₁ hV₂)
  have htwo := stmt11_5_3_two hTwo hCard h1102 h1003 h1141 h1142 h1151 h hV₁ hK
  obtain ⟨m, hm, hr, hmV₂⟩ : ∃ m : ℕ, n + 1 < m ∧ ((m : ℕ) : ℕ∞) ≤ E3.rParam (fsuV T I) ∧
      E3.mQuot (fsuV T I) V₂ < m := by
    rcases hkind with hSL | hSp
    · have := hq2 _ ((hCard G T L I n hset).1 hSL)
      exact ⟨2 * n, by omega, htwo.1 hSL, by omega⟩
    · have := hq2 _ ((hCard G T L I n hset).2 hSp)
      exact ⟨3 * n, by omega, htwo.2 hSp, by omega⟩
  have hV₂M : Subgroup.centralizer (V₂ : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    refine le_trans ?_ (SecA.normalizer_fsuV_le h331 h)
    by_contra hnc
    have h1 := E3.rParam_le_mQuot hV₂V hnc
    have h2 : ((m : ℕ) : ℕ∞) ≤ E3.mQuot (fsuV T I) V₂ := hr.trans h1
    exact absurd (by exact_mod_cast h2) (not_le.mpr hmV₂)
  obtain ⟨z, hzV₁, hz1, hzT⟩ := exists_z h hV₁
  have hzV : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) :=
    ⟨SecA.IsVi.le_fsuV hV₁ hzV₁, hzT⟩
  have hGz : ¬ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    fun hle => (h1143 G T L I n V₁ h hV₁ z hzV hz1).2.1 hK (inf_le_left.trans hle)
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hzT) t ht
  have hzT2 : IsPGroup 2 (Subgroup.zpowers z) := h.fsu.sylow.1.to_le
    (Subgroup.zpowers_le.mpr ((SecA.IsVi.le_fsuV hV₁).trans (SecA.fsuV_le_T h) hzV₁))
  have hInH : InH T (Subgroup.centralizer ({z} : Set G)) :=
    inH_of_le hTz (Subgroup.zpowers_le.mpr hzC) hzT2 (Subgroup.zpowers_ne_bot.mpr hz1)
      fun x hx => mem_normalizer_zpowers_of_mem_centralizer hx
  obtain ⟨H, hH, hHz⟩ := exists_isHStar_le _ _ rfl hInH hGz
  have hnH := h1144 G T L I n V₁ h hV₁ hK z hzV hz1 H hH hHz
  have hW₀ : ¬ E3.wClos (fsuV T I) 0 T ≤ pCoreOf 2 H :=
    (h1125 G T L I n V₁ V₂ H h hV₁ hV₂ hH.1 hH.2.1 fun _ => hV₂M).resolve_right
      (not_not.mpr habel)
  have hs : 1 < E3.sParam hVel := by
    by_cases hG2 : KindG2 L (fsuV T I) n
    · have := (h1122 G T L I n (2 * n) V₁ V₂ h hV₁ hV₂ (Or.inl ⟨hG2, rfl⟩)).2.2.2.1 hVel
      omega
    · have := (h1122 G T L I n n V₁ V₂ h hV₁ hV₂ (Or.inr ⟨hG2, rfl⟩)).2.2.2.1 hVel
      omega
  have hTH : T ≤ H := hH.1.1
  have hsylH := isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTH
  have h19 := E3.e3_19 hVel (S := T) (H := H) ⟨hsylH.1, hsylH.2.1, hsylH.2.2⟩ (i := 0) hnH
    (by simpa using hs)
  rw [zero_add] at h19
  apply hH.2.1
  rw [← h19]
  refine sup_le ?_ ?_
  · have hle := le_cClos_of_abelian hRank hComm h hset hkind hV₁ hV₂ hone hm hr habel
    exact inf_le_right.trans ((Subgroup.centralizer_le hle).trans hV₂M)
  · by_contra hNM
    have hWH : E3.wClos (fsuV T I) 0 T ≤ H := (E3.wClos_le _ _).trans hTH
    have hTN : T ≤ Subgroup.normalizer (E3.wClos (fsuV T I) 0 T : Set G) :=
      Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos T)
    have hQ := pCoreOf_two_le_of_isSylowTwoOf hsylH
    have hInH' : InH T (H ⊓ Subgroup.normalizer (E3.wClos (fsuV T I) 0 T : Set G)) :=
      inH_of_le (le_inf hTH hTN) (hQ.trans (le_inf hTH hTN))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hH.1.2
        (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
    have heq := hH.2.2 _ hInH' inf_le_left hNM
    apply hW₀
    have hHN : H ≤ Subgroup.normalizer (E3.wClos (fsuV T I) 0 T : Set G) := by
      rw [← heq]
      exact inf_le_right
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.le_pCoreOf 2 hWH
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hWH).2 hHN)
      (h.fsu.sylow.1.to_le (E3.wClos_le _ _))

theorem stmt11_5_3_of (hTwo : TwoPointsFact) (hCard : CardVFact) (hRank : RankV2Fact)
    (hComm : PointCommFact) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1003 : Stmt11_0_3)
    (h1110 : Stmt11_1_0) (h1122 : Stmt11_2_2) (h1125 : Stmt11_2_5) (h1141 : Stmt11_4_1)
    (h1142 : Stmt11_4_2) (h1143 : Stmt11_4_3) (h1144 : Stmt11_4_4) (h1151 : Stmt11_5_1) :
    Stmt11_5_3 := by
  intro G _ _ T L I n V₁ h hV₁ hK
  have htwo := stmt11_5_3_two hTwo hCard h1102 h1003 h1141 h1142 h1151 h hV₁ hK
  exact ⟨fun g hg => stmt11_5_3_one hTwo h1102 h1003 h1141 h1142 h1151 h hV₁ hK hg, htwo.1,
    htwo.2, stmt11_5_3_three hTwo hCard hRank hComm h331 h1102 h1003 h1110 h1122 h1125 h1141
      h1142 h1143 h1144 h1151 h hV₁ hK⟩

end CFSG.Quasithin.Vol2.Ch11.SecD
