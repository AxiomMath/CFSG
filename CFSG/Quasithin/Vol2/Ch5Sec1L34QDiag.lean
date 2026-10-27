module

public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Z1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

theorem ordTwistedA_two_eq (q : ℕ) (hq1 : 1 ≤ q) :
    ordTwistedA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) := by
  have hprod : (∏ i ∈ Finset.Icc 2 (2 + 1), (((q : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) =
      (q ^ 2 - 1) * (q ^ 3 + 1) := by
    rw [show Finset.Icc 2 (2 + 1) = {2, 3} by decide, Finset.prod_pair (by norm_num)]
    have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
    have e1 : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hq2]; ring
    have e2 : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [e1, e2, Int.toNat_natCast, Int.toNat_natCast]
  unfold ordTwistedA
  rw [hprod]

theorem ordTwistedA_two_ne (k : ℕ) : ordTwistedA 2 (2 ^ k) ≠ 20160 := by
  rw [ordTwistedA_two_eq _ Nat.one_le_two_pow]
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k <;> decide
  · have hq8 : 8 ≤ 2 ^ k := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    generalize 2 ^ k = q at hq8 ⊢
    have hg : Nat.gcd 3 (q + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    have hgpos : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hle : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / 3 ≤
        q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) := Nat.div_le_div_left hg hgpos
    have h3 : 512 ≤ q ^ 3 := by
      calc 512 = 8 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq8 3
    have h2 : 63 ≤ q ^ 2 - 1 := by
      have : 64 ≤ q ^ 2 := by
        calc 64 = 8 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left hq8 2
      omega
    have hlt : 20161 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / 3 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      calc 20161 * 3 ≤ 512 * (63 * 513) := by norm_num
        _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
          Nat.mul_le_mul h3 (Nat.mul_le_mul h2 (by omega))
    omega

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem le_pCoreOf_K_of_normal
    {P : Subgroup G} (hPK : P ≤ oTwoUpper H)
    (hKP : oTwoUpper H ≤ Subgroup.normalizer (P : Set G)) (hnot : ¬ oTwoUpper H ≤ P) :
    P ≤ pCoreOf 2 (oTwoUpper H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper H with hKdef
  have hsimp := h.isSimple_K
  have hPn : (P.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPK).mpr hKP
  rcases hsimp.eq_bot_or_eq_top_of_normal ((P.subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) with hb | ht
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
    intro x hx
    have hxN : (⟨x, hPK hx⟩ : ↥K) ∈ P.subgroupOf K := by
      rw [Subgroup.mem_subgroupOf]; exact hx
    have hxP : (⟨x, hPK hx⟩ : ↥K) ∈ CFSG.Open.pCore 2 ↥K := by
      exact hb hxN
    exact ⟨_, hxP, rfl⟩
  · exfalso
    apply hnot
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyH, hyo⟩
    have hyK : y ∈ K := mem_oTwoUpper_of_odd hyH hyo
    have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ⟨y, hyK⟩ ∈
        (P.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
      rw [ht]; exact Subgroup.mem_top _
    obtain ⟨c, hc, hcy⟩ := hmem
    have ho' : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (c⁻¹ * ⟨y, hyK⟩) = 1 := by
      rw [map_mul, map_inv, hcy, inv_mul_cancel]
    have ho : c⁻¹ * ⟨y, hyK⟩ ∈ CFSG.pCore 2 ↥K := by
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ho'
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup ⟨_, ho⟩
    have hk' : (c⁻¹ * ⟨y, hyK⟩) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hσc : (QuotientGroup.mk' (P.subgroupOf K)) c = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hc
    have hσy : (QuotientGroup.mk' (P.subgroupOf K)) ⟨y, hyK⟩ =
        (QuotientGroup.mk' (P.subgroupOf K)) (c⁻¹ * ⟨y, hyK⟩) := by
      rw [map_mul, map_inv, hσc, inv_one, one_mul]
    have hpow : (QuotientGroup.mk' (P.subgroupOf K)) ((⟨y, hyK⟩ : ↥K) ^ 2 ^ k) = 1 := by
      rw [map_pow, hσy, ← map_pow, hk', map_one]
    have hmemN : (⟨y, hyK⟩ : ↥K) ^ 2 ^ k ∈ P.subgroupOf K := by
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hpow
    rw [Subgroup.mem_subgroupOf] at hmemN
    have hyk : y ^ 2 ^ k ∈ P := by simpa using hmemN
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hyo) : Nat.Coprime (2 ^ k) (orderOf y))
    rw [← hm]
    exact P.pow_mem hyk m

theorem not_isBender
    {k : ℕ} : ¬ IsBenderCh5 k (O2Q (oTwoUpper H)) := by
  have hcard := card_of_lieModel_L34 h.l34
  rintro (hL2 | hSz | ⟨-, hU⟩)
  · rcases Nat.eq_zero_or_pos k with hk0 | hk
    · subst hk0
      rcases hL2 with ⟨-, -, K, _, _, hK, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · have := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K)
        rw [hK, pow_zero] at this
        omega
      all_goals exact absurd h0 (by norm_num)
    have h1 := card_of_lieModel_L2 hk hL2
    rw [hcard] at h1
    rcases Nat.lt_or_ge k 6 with hk6 | hk6
    · interval_cases k <;> omega
    · have h64 : 64 ≤ 2 ^ k := by
        calc 64 = 2 ^ 6 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk6
      have h4 : 4096 ≤ 4 ^ k := by
        calc 4096 = 4 ^ 6 := by norm_num
          _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hk6
      have : 64 * 4095 ≤ 2 ^ k * (4 ^ k - 1) := Nat.mul_le_mul h64 (by omega)
      omega
  · obtain ⟨a, ha, hka, h1⟩ := card_of_suzukiModel hSz
    rw [hcard] at h1
    have h8 : 8 ≤ 2 ^ k := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h64 : 64 ≤ (2 ^ k) ^ 2 := by
      calc 64 = 8 ^ 2 := by norm_num
        _ ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left h8 2
    have : 64 * 7 * 65 ≤ (2 ^ k) ^ 2 * (2 ^ k - 1) * ((2 ^ k) ^ 2 + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h64 (by omega)) (by omega)
    omega
  · have := h.isSimple_K
    have hZ : Subgroup.center (O2Q (oTwoUpper H)) = ⊥ := h.center_K_eq_bot
    have hcardQ : Nat.card (O2Q (oTwoUpper H) ⧸ Subgroup.center (O2Q (oTwoUpper H))) =
        20160 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center (O2Q (oTwoUpper H)))
      have h2 : Nat.card ↥(Subgroup.center (O2Q (oTwoUpper H))) = 1 := by
        rw [hZ, Subgroup.card_bot]
      rw [h2, mul_one] at h1
      exact h1.symm.trans hcard
    rcases hU with ⟨-, hU⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two hU).2.1 rfl
      rw [hcardQ] at h1
      exact ordTwistedA_two_ne k (by simpa using h1.symm)
    all_goals exact absurd h0 (by norm_num)

theorem isDiagramNontrivial
    (h510 : Stmt5_1_10) :
    E2.IsDiagramNontrivial T (oTwoUpper H) (T ⊓ oTwoUpper H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, -, -, -, K₁, hK₁, -, hcases⟩ := h510 G T M L H B D n h.hyp h.notation59
  rcases hcases with ⟨hlt, -⟩ | ⟨-, hBen⟩ | ⟨-, -, hd⟩
  · exfalso
    obtain ⟨hne, hperf, hsub, -⟩ := hK₁
    have hsubK : IsSubnormal K₁ (oTwoUpper H) :=
      A3.subnormal_of_le_of_le hsub hlt.le (oTwoUpper_le H)
    obtain ⟨P, hPK, hPn, hK₁P⟩ := A3.subnormal_exists_normal_of_lt hsubK hlt
    have hPO := h.le_pCoreOf_K_of_normal hPK.le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hPK.le).mp hPn)
      (fun hKP => hPK.ne (le_antisymm hPK.le hKP))
    have h2 : IsPGroup 2 ↥K₁ := (pCoreOf_isPGroup 2 _).to_le (hK₁P.trans hPO)
    have hsolv : Group.IsSolvable ↥K₁ := by
      have := h2.isNilpotent
      infer_instance
    apply hne
    have h3 := (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot K₁).mp hsolv
    rwa [(CFSG.Quasithin.perfectCore_eq_self_iff K₁).mpr hperf] at h3
  · exact absurd hBen h.not_isBender
  · exact hd

end Hyp5_1_14

end CFSG.Quasithin.H13
