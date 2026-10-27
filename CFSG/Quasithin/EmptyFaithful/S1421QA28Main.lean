module

public import CFSG.Quasithin.EmptyFaithful.S1421QA28Defs
public import CFSG.Quasithin.EmptyFaithful.S1421QA28Rows
public import CFSG.Quasithin.EmptyFaithful.S1421QA18Main
public import CFSG.Quasithin.Vol2.Ch1List
public import CFSG.Quasithin.Vol2.Ch11SecA11Bar
public import CFSG.Adapters.LinearFieldTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace QA28

section Numbers

theorem eq_zero_of_dvd {j m : ℕ} (hm : Odd m) (h : 504 * 2 ^ j ∣ 8 * m) : j = 0 := by
  by_contra hj
  have h1 : 8 * (63 * 2 ^ j) ∣ 8 * m := by
    rwa [show 8 * (63 * 2 ^ j) = 504 * 2 ^ j by ring]
  have h2 : 63 * 2 ^ j ∣ m := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have h3 : 2 ∣ m := (dvd_pow_self 2 hj).trans ((dvd_mul_left (2 ^ j) 63).trans h2)
  obtain ⟨k, hk⟩ := hm
  omega

theorem not_two_pow_six_dvd {m : ℕ} (hm : Odd m) (h : 2 ^ 6 ∣ 8 * m) : False := by
  obtain ⟨k, hk⟩ := hm
  omega

end Numbers

section Setting

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_quot_eq {H T : Subgroup G} (hT : IsSylowTwoOf T H) (hTc : Nat.card ↥T = 2 ^ 12)
    (hN : Nat.card ↥(pCoreOf 2 H) = 2 ^ 9) :
    ∃ m : ℕ, Odd m ∧ Nat.card (↥H ⧸ CFSG.pCore 2 ↥H) = 8 * m := by
  have hN' : Nat.card ↥(CFSG.pCore 2 ↥H) = 2 ^ 9 := by
    have h3 : Nat.card ↥(pCoreOf 2 H) = Nat.card ↥(CFSG.Open.pCore 2 ↥H) :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [← h3]
    exact hN
  obtain ⟨hTH, -, hidx⟩ := hT
  have e1 : Nat.card ↥(T.subgroupOf H) = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  have e2 := Subgroup.card_mul_index (T.subgroupOf H)
  have e3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥H)
  rw [e1, hTc] at e2
  rw [hN'] at e3
  refine ⟨(T.subgroupOf H).index, Nat.odd_iff.mpr (by omega), ?_⟩
  have h4 : Nat.card (↥H ⧸ CFSG.pCore 2 ↥H) * 2 ^ 9 = (8 * (T.subgroupOf H).index) * 2 ^ 9 := by
    rw [← e3, show (8 * (T.subgroupOf H).index) * 2 ^ 9 = 2 ^ 12 * (T.subgroupOf H).index by ring,
      e2]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h4

theorem card_T_eq {T M H K1 : Subgroup G} (st : Setting1427 T M H K1)
    (hsurv : Survivor4LegacyBare K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1)) (hTK : T ≤ K1) :
    Nat.card ↥T = 2 ^ 12 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hq1, hsp, -, -⟩ := hsurv
  have hK1card : Nat.card ↥K1 = 258048 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥K1)
    have h2 : Nat.card (OTwoQuot K1) = 2 ^ 3 * (4 ^ 3 - 1) :=
      IsL2Quot.card (by norm_num) hq1
    have h3 : Nat.card ↥(pCoreOf 2 K1) = Nat.card ↥(CFSG.Open.pCore 2 ↥K1) :=
      Subgroup.card_map_of_injective K1.subtype_injective
    have h4 : Nat.card ↥(pCoreOf 2 K1) = 2 ^ (1 + 2 * 4) := hsp.2.1
    rw [h1, ← h3, h4]
    exact (congrArg (· * 2 ^ (1 + 2 * 4)) h2).trans (by norm_num)
  have hsyl : Nat.card ↥(T ⊓ K1) = 2 ^ 12 := by
    have h1 := IsSylowTwoOf.card_eq st.notation_.sylow
    rw [h1, twoPart, hK1card, Nat.factorization_def _ Nat.prime_two,
      show (258048 : ℕ) = 2 ^ 12 * 63 by norm_num,
      padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rwa [inf_eq_left.mpr hTK] at hsyl

omit [Finite G] in
theorem coe_mem_pCoreOf {H : Subgroup G} (y : ↥H) (hy : y ∈ CFSG.pCore 2 ↥H) :
    (y : G) ∈ pCoreOf 2 H := by
  refine ⟨y, ?_, rfl⟩
  exact hy

omit [Finite G] in
theorem le_of_modO2Image_le {H L K : Subgroup G} (hLH : L ≤ H) (hO : pCoreOf 2 H ≤ K)
    (h : modO2Image H L ≤ modO2Image H K) : L ≤ K := by
  intro l hl
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨l, hLH hl⟩ : ↥H) ∈ modO2Image H K :=
    h (Subgroup.mem_map.mpr ⟨⟨l, hLH hl⟩, hl, rfl⟩)
  obtain ⟨k, hk, hkl⟩ := Subgroup.mem_map.mp hmem
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkl
  have h2 : ((k⁻¹ * ⟨l, hLH hl⟩ : ↥H) : G) ∈ K := hO (coe_mem_pCoreOf _ hkl)
  have hkK : (k : G) ∈ K := hk
  have e : l = (k : G) * ((k⁻¹ * ⟨l, hLH hl⟩ : ↥H) : G) := by simp
  rw [e]
  exact K.mul_mem hkK h2

theorem isPSL_modO2Image {H K : Subgroup G} (hKH : K ≤ H) (h : IsL2Quot 3 (OTwoQuot K)) :
    IsPSL 2 2 3 (ModO2 (modO2Image H K)) := by
  obtain ⟨e⟩ := h
  have e1 : ModO2 K ≃* OTwoQuot K := QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)
  have hcard : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by omega)
  have h1 : IsPSL 2 2 3 (ModO2 K) := by
    refine ⟨⟨Nat.prime_two, by omega, le_rfl, fun h => ?_, fun h => ?_⟩, GaloisField 2 3,
      inferInstance, inferInstance, hcard,
      ⟨(e1.trans e).trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL (GaloisField 2 3)
        2 2 3 (by omega) hcard).symm⟩⟩
    · have := congrArg Prod.snd h
      simp only at this
      omega
    · have := congrArg Prod.snd h
      simp only at this
      omega
  obtain ⟨e2⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hKH
  exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv e2.symm h1

end Setting

theorem lemma14218KcEq_of_inputs_legacyBare
    (h312 : A312ForSQTK) (hO : D4Order) (hR : Rank2TwoPart) :
    Lemma14218KcEqLegacyBare := by
  intro G _ _ T M H K1 st h13 hsurv htail L hL hKL
  have hyp := st.hyp
  obtain ⟨hK, hST, hQ⟩ := htail
  have hS' : S1421.sOf T K1 = T := hST.symm
  have hTK : T ≤ K1 := S1421QA18.le_K1_of_order st hS' hsurv hO
  have hK1Mc : K1 ≤ mcOf T := S1421.K1_le_mcOf st
  obtain ⟨z, -, hz1, -, hzZ, -, -, -, -⟩ := S1421QA18.exists_z hyp
  have hne : pCoreOf 2 (mcOf T) ≠ ⊥ := fun hb =>
    hz1 (by simpa using
      (hb ▸ S1421QA18.omegaOneCenter_le_pCoreOf_mcOf hyp hzZ : z ∈ (⊥ : Subgroup G)))
  have hSylT : IsSylowTwoOf T (mcOf T) :=
    isSylowTwoOf_of_isSylowTwo hyp.sylow hyp.toQTFE14.t_le_mc
  have hSyl : IsSylowTwoOf (S1421.sOf T K1) (mcOf T) := by
    rw [hS']
    exact hSylT
  have hB : K1 ∈ lFamily (S1421.sOf T K1) := st.notation_.cComp_mem
  have hLMc : L ≤ mcOf T := le_of_mem_cComp hL
  have hlist := lemma_1_2_4_list hyp.qtke hyp.simple hyp.nonabelian h312 hne hSyl hK1Mc hB hL hKL
  have hN9 : Nat.card ↥(pCoreOf 2 (mcOf T)) = 2 ^ 9 := by
    rw [hQ]
    exact hsurv.2.2.1.2.1
  obtain ⟨m, hm, hHbar⟩ := card_quot_eq hSylT (card_T_eq st hsurv hTK) hN9
  have hBL : modO2Image (mcOf T) K1 ≤ modO2Image (mcOf T) L :=
    Subgroup.map_mono fun x hx => hKL hx
  have h28 : IsPSL 2 2 3 (ModO2 (modO2Image (mcOf T) K1)) :=
    isPSL_modO2Image hK1Mc hsurv.2.1
  have hB504 : Nat.card ↥(modO2Image (mcOf T) K1) = 504 := by
    obtain ⟨j, hj⟩ := Ch1Four.card_modO2_mul (H := ↥(modO2Image (mcOf T) K1))
    rw [QA28.card_modO2 h28] at hj
    have hdvd : Nat.card ↥(modO2Image (mcOf T) K1) ∣
        Nat.card (↥(mcOf T) ⧸ CFSG.pCore 2 ↥(mcOf T)) := Subgroup.card_subgroup_dvd_card _
    rw [hHbar, ← hj] at hdvd
    have hj0 := eq_zero_of_dvd hm hdvd
    rw [hj0, pow_zero, mul_one] at hj
    exact hj.symm
  rcases hlist with heq | hcase | hnq
  ·
    exact le_of_modO2Image_le hLMc (hQ.le.trans (pCoreOf_le 2 K1)) heq.symm.le
  ·
    exfalso
    obtain ⟨-, hRk, -⟩ := QA28.rows_l28 h28 hB504 hcase
    have hdvdB : 504 ∣ Nat.card ↥(modO2Image (mcOf T) L) := by
      have := Subgroup.card_dvd_of_le hBL
      rwa [hB504] at this
    have hdvdH : Nat.card ↥(modO2Image (mcOf T) L) ∣ 8 * m := by
      rw [← hHbar]
      exact Subgroup.card_subgroup_dvd_card _
    rcases hR _ hRk with h168 | h64
    · rw [h168] at hdvdB
      omega
    · exact not_two_pow_six_dvd hm (h64.trans hdvdH)
  ·
    exact (QA28.nonquasi_l28 h28 hB504 hBL hnq).elim

end QA28

end CFSG.Quasithin
