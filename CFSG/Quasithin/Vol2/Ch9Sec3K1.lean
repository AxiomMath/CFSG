module

public import CFSG.Quasithin.Vol2.Ch9Sec3Cart
public import CFSG.Quasithin.Vol2.Ch9Sec3Facts
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518D5

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {e : ↥(fsuV T I) ≃* Om4.VM F}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F}
  (hc : S.IsCoord e ψ)
include hc

theorem le_normalizer_of_le_normalizer_V1 (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    (h314 : A314Facts) (hA3 : A314ThreeNormFact) (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT F).prod (diagT F))
    {K B : Subgroup G} (hKl : K ∈ lFamily T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hB3 : Nat.card B = 3) (hBD : B ≤ D) (hBK : B ≤ K)
    (hBTK : B ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    (hKV : K ≤ Subgroup.normalizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G)) :
    D ≤ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfsu := S.hyp.fsu
  set V₁ := fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) with hV₁
  set G₁ := Subgroup.normalizer (V₁ : Set G) with hG₁
  have hTG₁ : T ≤ G₁ := S.T_le_normalizer_V1
  have hDG₁ : D ≤ G₁ := fun d hd => S.mem_normalizer_V1_of_mem_N0 (hD.1 hd)
  have hsyl : IsSylowTwoOf T G₁ :=
    CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow hTG₁
  have hV₁2 : IsPGroup 2 V₁ := S.isPGroup_fsuV.to_le inf_le_left
  have hV₁O : V₁ ≤ pCoreOf 2 G₁ :=
    CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer Subgroup.le_normalizer le_rfl hV₁2
  have hO : pCoreOf 2 G₁ ≠ ⊥ := fun h0 => hc.V1_ne_bot (le_bot_iff.mp (h0 ▸ hV₁O))
  have hOT : pCoreOf 2 G₁ ≤ T := F7.isSylowTwoOf_pCoreOf_le hsyl
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKl
  obtain ⟨K₁, hK₁, hKK₁⟩ := CFSG.Quasithin.lemma_1_2_4_exists hfsu.qtke hfsu.simple
    hfsu.nonabelian h37 h39 hO hsyl hKV hKl
  have hnorm := CFSG.Quasithin.lemma_1_2_4_normal hfsu.qtke hfsu.simple hfsu.nonabelian h37 h38
    hO hsyl hKl hKK₁ hK₁ hTK
  have hG₁K₁ : G₁ ≤ Subgroup.normalizer (K₁ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hK₁)).mp hnorm
  rcases eq_or_lt_of_le hKK₁ with heq | hlt
  · rw [heq]
    exact hDG₁.trans hG₁K₁
  obtain ⟨hltbar, h314bar⟩ := a314Statement_bar hfsu.qtke hfsu.simple hfsu.nonabelian h36 h312
    h314 hO hsyl hKV hKl hK₁ hlt hTK hKA
  have hQbar := sqtkHyp_quotient_of_pCoreOf_ne_bot hfsu.qtke hfsu.simple hfsu.nonabelian hO
  have hsylbar : IsSylowTwoOf (o2Img G₁ T) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hsyl) _
      (QuotientGroup.mk'_surjective _)
  have hKbar := modO2Image_mem_lFamily hsyl hKV hKl
  have hA5bar : IsAlt 5 (ModO2 (modO2Image G₁ K)) := by
    obtain ⟨e1⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hKV
    obtain ⟨e2⟩ := hKA
    exact ⟨e1.symm.trans e2⟩
  have hK₁bar := modO2Image_mem_cComp hK₁
  have hK₁n : (modO2Image G₁ K₁).Normal :=
    hnorm.map (QuotientGroup.mk' (CFSG.pCore 2 ↥G₁)) (QuotientGroup.mk'_surjective _)
  have hp3 : CFSG.Open.pRank 3 (⊤ : Subgroup (O2Q G₁)) ≤ 2 :=
    hQbar.sqt 3 Nat.prime_three (by norm_num)
  have hD3 : IsPGroup 3 D := hc.isPGroup_three h37c h38c h2 hD hdiag
  have hD3bar : IsPGroup 3 (modO2Image G₁ D) :=
    (hD3.comap_of_injective G₁.subtype G₁.subtype_injective).map _
  have hDab : ∀ x ∈ modO2Image G₁ D, ∀ y ∈ modO2Image G₁ D, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc.mul_comm_of_mem h37c h38c hD hdiag (Subgroup.mem_subgroupOf.mp hx)
      (Subgroup.mem_subgroupOf.mp hy))
  obtain ⟨hDT1, hDT2⟩ := S.exists_mul_eq_mul_hall hD
  have hDT := modO2Image_set_mul_comm hDG₁ hTG₁ hDT1 hDT2
  have hD3e : ∀ x ∈ modO2Image G₁ D, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have h3 : x ^ 3 = 1 := Subtype.ext (by
      simpa using hc.pow_three_eq_one h37c h38c h2 hD hdiag (Subgroup.mem_subgroupOf.mp hx))
    rw [h3, map_one]
  have hTKbar : o2Img G₁ T ≤
      Subgroup.normalizer ((modO2Image G₁ K : Subgroup (O2Q G₁)) : Set (O2Q G₁)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact o2Map_mem_normalizer (hTK (Subgroup.mem_subgroupOf.mp ht))
  have hcard : Nat.card ↥V₁ ≤ 4 := hc.card_V1_le.trans (by rw [hc.card, h2]; norm_num)
  have hK₁V : K₁ ≤ Subgroup.centralizer (V₁ : Set G) :=
    le_centralizer_of_perfect_of_card_le_four hcard (le_of_mem_cComp hK₁)
      (perfect_of_mem_cComp hK₁)
  have hDK₁ : ¬ modO2Image G₁ D ≤ modO2Image G₁ K₁ := by
    intro hle
    obtain ⟨d₀, hd₀D, hd₀V⟩ := hc.exists_not_mem_centralizer_V1 h2 hdiag
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥G₁) ⟨d₀, hDG₁ hd₀D⟩ ∈ modO2Image G₁ K₁ :=
      hle ⟨⟨d₀, hDG₁ hd₀D⟩, Subgroup.mem_subgroupOf.mpr hd₀D, rfl⟩
    obtain ⟨k, hk, hkd⟩ := hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkd
    have hoO : ((k⁻¹ * ⟨d₀, hDG₁ hd₀D⟩ : ↥G₁) : G) ∈ pCoreOf 2 G₁ := by
      exact ⟨_, hkd, rfl⟩
    set φ := V₁.normalizerMonoidHom with hφ
    have hφk : φ k = 1 := by
      have : k ∈ φ.ker := by
        rw [hφ, Subgroup.normalizerMonoidHom_ker]
        exact Subgroup.mem_subgroupOf.mpr (hK₁V (Subgroup.mem_subgroupOf.mp hk))
      exact this
    obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₁ ⟨_, hoO⟩
    have hφo : (φ (k⁻¹ * ⟨d₀, hDG₁ hd₀D⟩)) ^ 2 ^ m = 1 := by
      rw [← map_pow]
      have : (k⁻¹ * ⟨d₀, hDG₁ hd₀D⟩ : ↥G₁) ^ 2 ^ m = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hm)
      rw [this, map_one]
    have hφd : φ ⟨d₀, hDG₁ hd₀D⟩ = φ (k⁻¹ * ⟨d₀, hDG₁ hd₀D⟩) := by
      rw [map_mul, map_inv, hφk, inv_one, one_mul]
    have hd3 : (φ ⟨d₀, hDG₁ hd₀D⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨d₀, hDG₁ hd₀D⟩ : ↥G₁) ^ 3 = 1 :=
        Subtype.ext (by simpa using hc.pow_three_eq_one h37c h38c h2 hD hdiag hd₀D)
      rw [this, map_one]
    have hcop : Nat.gcd 3 (2 ^ m) = 1 := Nat.Coprime.pow_right m (by norm_num)
    have h1 : φ ⟨d₀, hDG₁ hd₀D⟩ = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hd3, hφd ▸ hφo⟩
      rwa [hcop, pow_one] at this
    apply hd₀V
    have : (⟨d₀, hDG₁ hd₀D⟩ : ↥G₁) ∈ φ.ker := h1
    rw [hφ, Subgroup.normalizerMonoidHom_ker] at this
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨⟨b, hbB⟩, hb3⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 3 (by rw [hB3])
  have hb3' : orderOf b = 3 := by rw [← Subgroup.orderOf_mk b hbB]; exact hb3
  have hbG₁ : b ∈ G₁ := hDG₁ (hBD hbB)
  have hb : ∃ y ∈ modO2Image G₁ K ⊓ modO2Image G₁ D, orderOf y = 3 ∧
      y ∈ Subgroup.normalizer ((o2Img G₁ T ⊓ modO2Image G₁ K : Subgroup (O2Q G₁)) :
        Set (O2Q G₁)) := by
    refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥G₁) ⟨b, hbG₁⟩,
      ⟨⟨⟨b, hbG₁⟩, Subgroup.mem_subgroupOf.mpr (hBK hbB), rfl⟩,
        ⟨⟨b, hbG₁⟩, Subgroup.mem_subgroupOf.mpr (hBD hbB), rfl⟩⟩, ?_, ?_⟩
    · have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥G₁) ⟨b, hbG₁⟩) ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨b, hbG₁⟩ : ↥G₁) ^ 3 = 1 := Subtype.ext (by simp [← hb3', pow_orderOf_eq_one])
        rw [this, map_one]
      have hne : QuotientGroup.mk' (CFSG.pCore 2 ↥G₁) ⟨b, hbG₁⟩ ≠ 1 := by
        intro h0
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h0
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥G₁)) ⟨_, h0⟩
        have hbk : b ^ 2 ^ k = 1 := by
          simpa using congrArg Subtype.val (congrArg Subtype.val hk)
        have := orderOf_dvd_of_pow_eq_one hbk
        rw [hb3'] at this
        have h3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
        omega
      have hdvd := orderOf_dvd_of_pow_eq_one h1
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h' | h'
      · exact absurd (orderOf_eq_one_iff.mp h') hne
      · exact h'
    · show _ ∈ Subgroup.normalizer ((modO2Image G₁ T ⊓ modO2Image G₁ K :
        Subgroup (O2Q G₁)) : Set (O2Q G₁))
      rw [← modO2Image_inf_eq hOT]
      exact o2Map_mem_normalizer (hBTK hbB)
  have hDK := hA3 (O2Q G₁) hQbar hp3 (o2Img G₁ T) (modO2Image G₁ K) (modO2Image G₁ K₁)
    (modO2Image G₁ D) hsylbar hKbar hA5bar hK₁bar hltbar h314bar hK₁n hD3bar hDab hDT hDK₁ hb
    hTKbar hD3e
  intro d hd
  exact mem_normalizer_of_mk_mem_normalizer hKV hperf (hOT.trans hTK) (hDG₁ hd)
    (hDK ⟨⟨d, hDG₁ hd⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩)

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
