module

public import CFSG.Quasithin.Vol2.Ch9Sec3FactsFF
public import CFSG.Quasithin.Vol2.Ch9Sec3FactsFFE9
public import CFSG.Quasithin.Vol2.Ch9Sec3CartE9
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDGroup
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113FourA7
public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrL
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518D5
public import CFSG.Quasithin.Vol2.Ch9Sec3Facts

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

theorem pCore_eq_bot_of_normal {Y : Type*} [Group Y] (h : CFSG.pCore 2 Y = ⊥) {N : Subgroup Y}
    (hN : N.Normal) : CFSG.pCore 2 ↥N = ⊥ := by
  have h1 := CFSG.ABGLocalTools.map_pCore_le_of_injective_of_normal (p := 2) N.subtype
    N.subtype_injective (by rw [Subgroup.range_subtype]; exact hN)
  rw [h, le_bot_iff] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp h1

theorem le_omegaOneCenter {G : Type*} [Group G] {T W : Subgroup G} (hWT : W ≤ T)
    (hWC : W ≤ Subgroup.centralizer (T : Set G)) (hW : ∀ w ∈ W, w ^ 2 = 1) :
    W ≤ quasithinOmegaOneCenter T := fun w hw =>
  Subgroup.subset_closure ⟨⟨hWT hw, hWC hw⟩, hW w hw⟩

theorem mem_normalizer_sup_of_map_le {G : Type*} [Group G] [Finite G] {A C : Subgroup G} {x : G}
    (hA : A.map (MulAut.conj x).toMonoidHom ≤ A ⊔ C)
    (hC : C.map (MulAut.conj x).toMonoidHom ≤ A ⊔ C) :
    x ∈ Subgroup.normalizer ((A ⊔ C : Subgroup G) : Set G) := by
  have hle : (A ⊔ C).map (MulAut.conj x).toMonoidHom ≤ A ⊔ C := by
    rw [Subgroup.map_sup]
    exact sup_le hA hC
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj x).injective).ge)

theorem mem_normalizer_of_mem_centralizer {G : Type*} [Group G] {A : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.centralizer (A : Set G)) : x ∈ Subgroup.normalizer (A : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun a => ⟨fun ha => ?_, fun ha => ?_⟩
  · have h := Subgroup.mem_centralizer_iff.mp hx a ha
    rw [← h, mul_inv_cancel_right]
    exact ha
  · have h := Subgroup.mem_centralizer_iff.mp hx _ ha
    have e : a = x * a * x⁻¹ := by
      have h2 : x * a = x * (x * a * x⁻¹) := by rw [← h]; group
      exact mul_left_cancel h2
    rw [e]
    exact ha

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {e : ↥(fsuV T I) ≃* Om4.VM F}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F}
  (hc : S.IsCoord e ψ)
include hc

theorem exists_conj_of_mem_V1 (h2 : n = 2) (h1 : zQ T I = fsuV T I) {D : Subgroup G}
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT F).prod (diagT F)) {v : G}
    (hv : v ∈ fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)) :
    ∃ d ∈ D, ∃ z ∈ quasithinOmegaOneCenter T, v = d * z * d⁻¹ := by
  have hK4 : Fintype.card F = 4 := by rw [hc.card, h2]; norm_num
  have hev := hc.toAdd_e_eq hv
  set c := (Multiplicative.toAdd (e ⟨v, hv.1⟩) : Matrix (Fin 2) (Fin 2) F) 0 0 with hcdef
  have hev' : e ⟨v, hv.1⟩ = Multiplicative.ofAdd (c • !![(1 : F), 0; 0, 0]) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    exact hev
  by_cases hc0 : c = 0
  · have hv1 : v = 1 := by
      have h3 : e ⟨v, hv.1⟩ = 1 := by rw [hev', hc0, zero_smul]; rfl
      exact congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h3)
    exact ⟨1, D.one_mem, 1, Subgroup.one_mem _, by rw [hv1]; group⟩
  obtain ⟨z, hzV, hzZ, c₀, hc₀, hze⟩ := hc.exists_z h1
  set q := Units.mk0 (c / c₀) (div_ne_zero hc0 hc₀) with hq
  obtain ⟨d, hdD, hdL, hψd⟩ := exists_mem_of_diag hdiag (q ^ 2) (q ^ 2)
  have hq4 : ((q ^ 2 : Fˣ) : F) * ((q ^ 2 : Fˣ) : F) = c / c₀ := by
    have h3 := pow_three_eq_one_of_card_four hK4 q
    have : (q ^ 2) * (q ^ 2) = q := by
      calc q ^ 2 * q ^ 2 = q ^ 3 * q := by group
        _ = q := by rw [h3, one_mul]
    rw [← Units.val_mul, this, hq, Units.val_mk0]
  have h3 : bar e (Subgroup.inclusion S.L0_le_normalizer_V ⟨d, hdL⟩) (e ⟨z, hzV⟩) =
      e ⟨v, hv.1⟩ := by
    rw [hc.bar_L0, hψd, hze, rho_diag_smul_e11, hev', hq4, div_mul_cancel₀ c hc₀]
  rw [bar_apply] at h3
  exact ⟨d, hdD, z, hzZ, (congrArg Subtype.val (e.injective h3)).symm⟩

variable {D : Subgroup G}

theorem le_normalizer_or_of_pCoreOf_ne_bot (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    (h314 : A314Facts) (hA3 : A314ThreeNormFact) (hFC : A314InnerLieFact)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT F).prod (diagT F))
    {X K B : Subgroup G} (hTX : T ≤ X) (hDX : D ≤ X) (hKX : K ≤ X) (hO : pCoreOf 2 X ≠ ⊥)
    (hKl : K ∈ lFamily T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hB3 : Nat.card B = 3) (hBD : B ≤ D) (hBK : B ≤ K)
    (hBTK : B ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) :
    D ≤ Subgroup.normalizer (K : Set G) ∨ ∃ KX : Subgroup G, KX ∈ cComp X ∧ K < KX ∧
      X ≤ Subgroup.normalizer (KX : Set G) ∧ D ≤ KX ∧
      ((IsSL3 4 (O2Q KX) ∨ IsPSp4 2 2 (O2Q KX) ∨ IsG2 2 2 (O2Q KX)) →
        D ≤ Subgroup.normalizer (K : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfsu := S.hyp.fsu
  have hsyl : IsSylowTwoOf T X := CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow hTX
  have hOT : pCoreOf 2 X ≤ T := F7.isSylowTwoOf_pCoreOf_le hsyl
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKl
  obtain ⟨KX, hKXc, hKKX⟩ := CFSG.Quasithin.lemma_1_2_4_exists hfsu.qtke hfsu.simple
    hfsu.nonabelian h37 h39 hO hsyl hKX hKl
  have hnorm := CFSG.Quasithin.lemma_1_2_4_normal hfsu.qtke hfsu.simple hfsu.nonabelian h37 h38
    hO hsyl hKl hKKX hKXc hTK
  have hXKX : X ≤ Subgroup.normalizer (KX : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hKXc)).mp hnorm
  rcases eq_or_lt_of_le hKKX with heq | hlt
  · left
    rw [heq]
    exact hDX.trans hXKX
  obtain ⟨hltbar, h314bar⟩ := a314Statement_bar hfsu.qtke hfsu.simple hfsu.nonabelian h36 h312
    h314 hO hsyl hKX hKl hKXc hlt hTK hKA
  have hQbar := sqtkHyp_quotient_of_pCoreOf_ne_bot hfsu.qtke hfsu.simple hfsu.nonabelian hO
  have hsylbar : IsSylowTwoOf (o2Img X T) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hsyl) _
      (QuotientGroup.mk'_surjective _)
  have hKbar := modO2Image_mem_lFamily hsyl hKX hKl
  have hA5bar : IsAlt 5 (ModO2 (modO2Image X K)) := by
    obtain ⟨e1⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hKX
    obtain ⟨e2⟩ := hKA
    exact ⟨e1.symm.trans e2⟩
  have hKXbar := modO2Image_mem_cComp hKXc
  have hKXn : (modO2Image X KX).Normal :=
    hnorm.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (QuotientGroup.mk'_surjective _)
  have hp3 : CFSG.Open.pRank 3 (⊤ : Subgroup (O2Q X)) ≤ 2 :=
    hQbar.sqt 3 Nat.prime_three (by norm_num)
  have hD3 : IsPGroup 3 D := hc.isPGroup_three h37c h38c h2 hD hdiag
  have hD3bar : IsPGroup 3 (modO2Image X D) :=
    (hD3.comap_of_injective X.subtype X.subtype_injective).map _
  have hDab : ∀ x ∈ modO2Image X D, ∀ y ∈ modO2Image X D, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc.mul_comm_of_mem h37c h38c hD hdiag (Subgroup.mem_subgroupOf.mp hx)
      (Subgroup.mem_subgroupOf.mp hy))
  obtain ⟨hDT1, hDT2⟩ := S.exists_mul_eq_mul_hall hD
  have hDT := modO2Image_set_mul_comm hDX hTX hDT1 hDT2
  have hD3e : ∀ x ∈ modO2Image X D, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have h3 : x ^ 3 = 1 := Subtype.ext (by
      simpa using hc.pow_three_eq_one h37c h38c h2 hD hdiag (Subgroup.mem_subgroupOf.mp hx))
    rw [h3, map_one]
  have hTKbar : o2Img X T ≤
      Subgroup.normalizer ((modO2Image X K : Subgroup (O2Q X)) : Set (O2Q X)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact o2Map_mem_normalizer (hTK (Subgroup.mem_subgroupOf.mp ht))
  obtain ⟨⟨b, hbB⟩, hb3⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 3 (by rw [hB3])
  have hb3' : orderOf b = 3 := by rw [← Subgroup.orderOf_mk b hbB]; exact hb3
  have hbX : b ∈ X := hDX (hBD hbB)
  have hb : ∃ y ∈ modO2Image X K ⊓ modO2Image X D, orderOf y = 3 ∧
      y ∈ Subgroup.normalizer ((o2Img X T ⊓ modO2Image X K : Subgroup (O2Q X)) :
        Set (O2Q X)) := by
    refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨b, hbX⟩,
      ⟨⟨⟨b, hbX⟩, Subgroup.mem_subgroupOf.mpr (hBK hbB), rfl⟩,
        ⟨⟨b, hbX⟩, Subgroup.mem_subgroupOf.mpr (hBD hbB), rfl⟩⟩, ?_, ?_⟩
    · have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨b, hbX⟩) ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨b, hbX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simp [← hb3', pow_orderOf_eq_one])
        rw [this, map_one]
      have hne : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨b, hbX⟩ ≠ 1 := by
        intro h0
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h0
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) ⟨_, h0⟩
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
    · show _ ∈ Subgroup.normalizer ((modO2Image X T ⊓ modO2Image X K :
        Subgroup (O2Q X)) : Set (O2Q X))
      rw [← modO2Image_inf_eq hOT]
      exact o2Map_mem_normalizer (hBTK hbB)
  have hlift : modO2Image X D ≤ Subgroup.normalizer ((modO2Image X K : Subgroup (O2Q X)) :
      Set (O2Q X)) → D ≤ Subgroup.normalizer (K : Set G) := fun hDK d hd =>
    mem_normalizer_of_mk_mem_normalizer hKX hperf (hOT.trans hTK) (hDX hd)
      (hDK ⟨⟨d, hDX hd⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩)
  by_cases hDKX : modO2Image X D ≤ modO2Image X KX
  · right
    have hDKO : D ≤ pCoreOf 2 X ⊔ KX := by
      intro d hd
      obtain ⟨k, hk, hkd⟩ := hDKX ⟨⟨d, hDX hd⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkd
      have hoO : ((k⁻¹ * ⟨d, hDX hd⟩ : ↥X) : G) ∈ pCoreOf 2 X := by
        exact ⟨_, hkd, rfl⟩
      have e : d = (k : G) * ((k⁻¹ * ⟨d, hDX hd⟩ : ↥X) : G) := by simp
      rw [e]
      exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hk))
        (Subgroup.mem_sup_left hoO)
    have hDKX' : D ≤ KX := Vol2.Ch10.SecB.C11AmS.le_of_odd hDKO hD.2.1
      (B6.isTwoQuotient_of_sup_eq (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
        (sup_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXKX) Subgroup.le_normalizer)
        rfl)
    refine ⟨KX, hKXc, hlt, hXKX, hDKX', fun hLie => hlift ?_⟩
    have hbot : CFSG.pCore 2 ↥(modO2Image X KX) = ⊥ := pCore_eq_bot_of_normal hQbar.o2 hKXn
    obtain ⟨e1⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv (le_of_mem_cComp hKXc)
    let e2 : ModO2 (modO2Image X KX) ≃* ↥(modO2Image X KX) :=
      (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
    let e : O2Q KX ≃* ↥(modO2Image X KX) := e1.trans e2
    have hLie' : IsSL3 4 ↥(modO2Image X KX) ∨ IsPSp4 2 2 ↥(modO2Image X KX) ∨
        IsG2 2 2 ↥(modO2Image X KX) :=
      hLie.imp (IsSL3.of_mulEquiv e) (Or.imp (IsPSp4.of_mulEquiv e) (IsG2.of_mulEquiv e))
    exact hFC (O2Q X) hQbar (o2Img X T) (modO2Image X K) (modO2Image X KX) (modO2Image X D)
      hsylbar hKbar hA5bar hKXbar hltbar h314bar hKXn hLie' hD3bar hDKX hDT hTKbar
  · left
    exact hlift (hA3 (O2Q X) hQbar hp3 (o2Img X T) (modO2Image X K) (modO2Image X KX)
      (modO2Image X D) hsylbar hKbar hA5bar hKXbar hltbar h314bar hKXn hD3bar hDab hDT hDKX hb
      hTKbar hD3e)

theorem false_of_pCoreOf_ne_bot (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    (h314 : A314Facts) (hA3 : A314ThreeNormFact) (hFB : A314FFFactE9) (hFC : A314InnerLieFact)
    (hFD : A7FFNoA5Fact) (h3108 : Stmt3_2_10_eight) (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2) (h1 : zQ T I = fsuV T I)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT F).prod (diagT F))
    {H K B : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hHK : H = K ⊔ T) (hKc : K ∈ cComp H)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hB3 : Nat.card B = 3) (hBD : B ≤ D) (hBK : B ≤ K)
    (hBTK : B ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    (hZK : K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hKV : ¬ K ≤ Subgroup.normalizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G))
    (hDK : ¬ D ≤ Subgroup.normalizer (K : Set G)) (hO : pCoreOf 2 (D ⊔ H) ≠ ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  set V₁ := fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) with hV₁
  set X := D ⊔ H with hXdef
  have hTH : T ≤ H := hH.1.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTX : T ≤ X := hTH.trans le_sup_right
  have hDX : D ≤ X := le_sup_left
  have hKX : K ≤ X := hKH.trans le_sup_right
  have hKl : K ∈ lFamily T := by
    show K ∈ cComp (K ⊔ T)
    rw [← hHK]
    exact hKc
  rcases hc.le_normalizer_or_of_pCoreOf_ne_bot h36 h37 h38 h39 h312 h314 hA3 hFC h37c h38c h2
      hD hdiag hTX hDX hKX hO hKl hTK hKA hB3 hBD hBK hBTK with hDN |
      ⟨KX, hKXc, hlt, hXKX, hDKX, hLie⟩
  · exact hDK hDN
  have hTXs : IsSylowTwoOf T X :=
    CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow hTX
  have hXchar : CharTwo X := charTwo_of_inH' hfsu.qtke hfsu.sylow ⟨hTX, hO⟩
  obtain ⟨hVXO, hVXe, hVXr⟩ :=
    conjClosure_isTwoReducedIn_of_charTwo hTXs hXchar (le_refl (quasithinOmegaOneCenter T))
  set VX := conjClosure (quasithinOmegaOneCenter T) X with hVX
  have hV₁VX : V₁ ≤ VX := by
    intro v hv
    obtain ⟨d, hd, z, hz, rfl⟩ := hc.exists_conj_of_mem_V1 h2 h1 hdiag hv
    exact Subgroup.subset_closure ⟨d, hDX hd, z, hz, rfl⟩
  have hKC : ¬ K ≤ Subgroup.centralizer (VX : Set G) := fun hle => hKV fun k hk =>
    mem_normalizer_of_mem_centralizer (Subgroup.centralizer_le hV₁VX (hle hk))
  have hJT : thompsonJ T ≤ T := thompsonJ_le_self T
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKc
  have hTHs : IsSylowTwoOf T H := CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow hTH
  have hHKn : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have hOK : pCoreOf 2 K ≤ T :=
    (CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH)
      (hHKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)).trans (F7.isSylowTwoOf_pCoreOf_le hTHs)
  have hVp : IsVplus T L I (fsuV T I) := by
    by_cases hc' : L ≠ conjClosure L T ∧ Case326VM T L I
    · exact Or.inl ⟨hc'.1, hc'.2, S.hVM⟩
    · exact Or.inr ⟨hc', rfl⟩
  have hJK : ¬ ⁅K, thompsonJ T⁆ ≤ pCoreOf 2 K := by
    intro hle
    set Sx := thompsonJ T ⊔ pCoreOf 2 K with hSx
    have hSxT : Sx ≤ T := sup_le hJT hOK
    have hKN : K ≤ Subgroup.normalizer (Sx : Set G) := by
      intro k hk
      refine mem_normalizer_sup_of_map_le ?_ ?_
      · rintro _ ⟨j, hj, rfl⟩
        show (MulAut.conj k) j ∈ Sx
        rw [MulAut.conj_apply]
        have hc1 : k * j * k⁻¹ * j⁻¹ ∈ pCoreOf 2 K :=
          hle (Subgroup.commutator_mem_commutator hk hj)
        have e : k * j * k⁻¹ = (k * j * k⁻¹ * j⁻¹) * j := by group
        rw [e]
        exact mul_mem (Subgroup.mem_sup_right hc1) (Subgroup.mem_sup_left hj)
      · rw [show (pCoreOf 2 K).map (MulAut.conj k).toMonoidHom = pCoreOf 2 K from
          Subgroup.mem_normalizer_iff_map_conj_eq.mp
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk)]
        exact le_sup_right
    have hNS := (h3108 G T L I (fsuV T I) hfsu hVp S.hJ Sx (hfsu.sylow.1.to_le hSxT)
      le_sup_left).2
    exact hH.2.1 (by rw [hHK]; exact sup_le (hKN.trans hNS) Setup.T_le_fsuM)
  have hKJ : ⁅K, thompsonJ T⁆ = K := by
    by_contra hne
    apply hJK
    have hs : IsSimpleGroup (O2Q K) := by
      obtain ⟨eA⟩ := hKA
      have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact eA.isSimpleGroup
    refine le_pCoreOf_of_normal_of_ne hperf hs ?_ (Subgroup.normalizer_commutator_ge_left K _) hne
    rw [Subgroup.commutator_le]
    intro k hk j hj
    have h3 : j * k⁻¹ * j⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hTK (hJT hj)) _).mp (K.inv_mem hk)
    rw [commutatorElement_def]
    have e : k * j * k⁻¹ * j⁻¹ = k * (j * k⁻¹ * j⁻¹) := by group
    rw [e]
    exact K.mul_mem hk h3
  have hJC : ¬ ⁅K, thompsonJ T⁆ ≤ Subgroup.centralizer (VX : Set G) := by rw [hKJ]; exact hKC
  have hSQX : SQTKGroup ↥X := sqtkGroup_of_pCoreOf_ne_bot hfsu.qtke hfsu.simple hfsu.nonabelian hO
  obtain ⟨a, haD, b, hbD, hab, ha3, hb3, ha1, hba⟩ := hc.exists_e9 h37c h38c h2 hD hdiag
  rcases hFB G X T K KX VX hSQX hTXs hKX hKl hTK hKA hKXc hlt hXKX hVXr hJC
      ⟨a, hDKX haD, b, hDKX hbD, hab, ha3, hb3, ha1, hba⟩ with
      hL | hL | hL | hA7
  · exact hDK (hLie (Or.inl hL))
  · exact hDK (hLie (Or.inr (Or.inl hL)))
  · exact hDK (hLie (Or.inr (Or.inr hL)))
  apply hFD G X T K KX VX hSQX hTXs hlt.le (le_of_mem_cComp hKXc) hXKX hperf hKA hTK hVXr hA7 hJC
  have hVXT : VX ≤ T := hVXO.trans (inf_le_left.trans (F7.isSylowTwoOf_pCoreOf_le hTXs))
  have hle : VX ⊓ Subgroup.centralizer (T : Set G) ≤ quasithinOmegaOneCenter T :=
    le_omegaOneCenter (inf_le_left.trans hVXT) inf_le_right (fun w hw => hVXe.2 w hw.1)
  exact hZK.trans (Subgroup.centralizer_le hle)

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
