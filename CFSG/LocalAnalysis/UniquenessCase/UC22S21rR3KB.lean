module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3F3S
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3NNOut
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3KA
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3HA
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3F3A
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3S13
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UCheap
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101USyl
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100Res2
import CFSG.LocalAnalysis.UniquenessCase.UC6S898b
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtyEightOq
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22r3k_exists_mem_centralizer {D : Data G}
    (hSg : UC6S846.SigmaStd D) (he : CFSG.Open.evenRank G = 3) {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : K ≠ L) (hset : conjSetOf D.M L = {L, K})
    {n : ℕ} (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {p : ℕ} (hp : p ∈ D.sig) (hpn : ¬ p ∣ n) :
    ∃ z ∈ centralizer ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) :
      Set (Bar2 D.M)), orderOf z = p := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨E, hEM, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hpp.one_lt D.M
  rw [uc22s2121e3_pRank_eq_three hSg he hp] at hEc
  have hEt : IsElemAbelian p (⊤ : Subgroup ↥E) := by
    have h := hE.subgroupOf E
    rwa [Subgroup.subgroupOf_self] at h
  have hodd : ∀ e : ↥E, Odd (orderOf (e : G)) := fun e =>
    (hpp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one (hE.2 e e.2))
  have hmemK : K ∈ conjSetOf D.M L := by rw [hset]; simp
  have hc2 : (conjSetOf D.M L).ncard = 2 := by rw [hset]; exact Set.ncard_pair hne.symm
  have hcK : (conjSetOf D.M K).ncard = 2 := by rw [uc22p2214_conjSetOf_eq hmemK]; exact hc2
  let φ : ↥E →* Bar2 D.M := (uc22p21cPi D.M).comp (Subgroup.inclusion hEM)
  have act : ∀ {Y : Subgroup G}, Y ∈ calC D.M → (conjSetOf D.M Y).ncard = 2 →
      (IsL2 (Bar2 Y) n ∨ IsSz (Bar2 Y) n) → ∃ N : Subgroup ↥E, N.index ≤ p ∧
        ∀ e ∈ N, ∀ f ∈ barImage D.M Y, φ e * f = f * φ e := by
    intro Y hY hcY hSY
    have hF := u4x_shape_barImage hY hSY
    refine uc22r3h_exists_centralizing hpp hEt (u4x_center_eq_bot hY hSY)
      (pRank_le_one_of_isL2_or_isSz hF hpp hp2) (fun α hα => ?_) φ fun e =>
        uc22ine229_mk_mem_normalizer (uc22p2214_mem_normalizer_of_odd hcY (hEM e.2) (hodd e))
    rcases hF with h | h
    · exact uc22p2214_inner_of_prime_L2 h hpp hpn hα
    · exact uc22p2214_inner_of_prime_Sz h hpp hpn hα
  obtain ⟨N₁, hN₁i, hN₁⟩ := act hL hc2 hS
  obtain ⟨N₂, hN₂i, hN₂⟩ := act hK hcK (uc22s21ru4e_shape_conj hmemK hS)
  obtain ⟨hcomm, -⟩ := u4x_bar_structure hL hK hne hset hS
  have hne' : N₁ ⊓ N₂ ≠ ⊥ := by
    intro hbot
    have hi := Subgroup.index_inf_le (H := N₁) (K := N₂)
    rw [hbot, Subgroup.index_bot, hEc] at hi
    have hlt : p * p < p ^ 3 := by
      rw [← sq]
      exact Nat.pow_lt_pow_right hpp.one_lt (by norm_num)
    have := hi.trans (Nat.mul_le_mul hN₁i hN₂i)
    omega
  obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne'
  have he1' : (e : G) ≠ 1 := fun h => he1 (Subtype.ext (Subtype.ext h))
  refine ⟨φ e, mem_centralizer_iff.2 fun h hh => ?_,
    orderOf_bar_eq_of_prime (hEM e.2) hpp hp2 (orderOf_eq_prime (hE.2 e e.2) he1')⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := u4x_mem_sup hcomm hh
  rw [mul_assoc, ← hN₂ e he.2 b hb, ← mul_assoc, ← hN₁ e he.1 a ha, mul_assoc]

theorem uc22r3k_false_of_le_two {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h15 : S21_15C D Ch) (hNN : R847E3ThinNNOut D) (h1930 : H1930 D)
    (c : Ctx21 D Ch) (he : CFSG.Open.evenRank G = 3) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {q : ℕ} (hSz : IsSz (Bar2 L) q) (hq : q.Prime)
    (hqn : ¬ q ∣ 2 ^ q - 1) {m : ℕ} (hm : Odd m) (hqm : q ∣ 2 ^ m - 1) {b : G} (hb : b ∈ c.B0)
    (hbo : orderOf b = q) (hbT : b ∈ normalizer (D.T : Set G)) (hbL : b ∈ normalizer (L : Set G))
    (hninn : ¬ ∃ y ∈ L, ∀ x ∈ L, b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M)
    (h52 : ¬ 3 ≤ CFSG.Open.pRank 5 D.M) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨K, hne, hset, hK⟩ := uc22s21ru4e_exists_second_member hc2 hL
  have hq7 := PartTwo.s13_seven_le_of_dvd hm hq hqm
  have hq2 : q ≠ 2 := by omega
  have h5L := uc22r3g_five_dvd_card hSz
  obtain ⟨a, haL, hao, hba⟩ := uc22r3g_exists_commute (by norm_num : Nat.Prime 5) hq hbo hbL
    (uc22r3g_not_dvd_card (Or.inr hSz) hq hq2 hqn hm hqm) h5L
    (PartTwo.S17.thin8_of_isSz hSz 5 (by norm_num) (by norm_num)) (by omega)
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  have : Fact p.Prime := ⟨hpP⟩
  have hpd := uc22r8100b_dvd_of_modEq (P2214S.sz_cong_of_s21_15C h15 h1930 c hL hc2 hSz hp)
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact UC6S898.not_three_dvd_two_pow_add_one_of_even (even_two_mul q) hpd
  have hpq : ¬ p ∣ q := fun hd => by
    have : Fact q.Prime := ⟨hq⟩
    rw [(Nat.prime_dvd_prime_iff_eq hpP hq).1 hd] at hpd
    have h5 : q ∣ 5 := by
      rw [← ZMod.natCast_eq_zero_iff] at hpd ⊢
      push_cast at hpd ⊢
      rw [pow_mul, ZMod.pow_card] at hpd
      linear_combination hpd
    have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).1 h5
    omega
  have hLN : ¬ (L.subgroupOf D.M).Normal := fun hN => by
    have hle := (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hN
    have h1 : conjSetOf D.M L ⊆ {L} := by
      rintro _ ⟨g, hg, rfl⟩
      exact mem_normalizer_iff_map_conj_eq.1 (hle hg)
    have := Set.ncard_le_ncard h1 (Set.finite_singleton L)
    rw [Set.ncard_singleton, hc2] at this
    omega
  have hNA : normalizer (zpowers a : Set G) ≤ D.M :=
    hNN L hL hLN (PartTwo.S17.thin8_of_isSz hSz) (zpowers a) (zpowers_le.2 haL) 5
      (by norm_num) (by norm_num) (by rw [Nat.card_zpowers, hao]) p hp
      (hpP.five_le_of_ne_two_of_ne_three hp2 hp3)
      fun h => hpq (h.trans (u81_card_outer_dvd (Or.inr hSz)))
  have hX5 : IsPGroup 5 ↥(zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao, pow_one])
  obtain ⟨R, hR, haR⟩ := PartTwo.exists_isSylowOf_ge_of_isPGroup hX5 (zpowers_le.2 (hL.1.le haL))
  have hn5 : ¬ 5 ∣ q := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hq).1 h
    omega
  obtain ⟨B, hBR, -, hBel, hΩ⟩ := uc22r3k_exists_omega hL hK hne hset (Or.inr hSz)
    Nat.prime_five (by norm_num) hn5 h5L (by omega) hR
  have hBX : barImage D.M B ≤ barImage D.M L ⊔ barImage D.M K := (barImage_mono hBR).trans
    (uc22r3k_barImage_le_sup hL hK hne hset (Or.inr hSz) Nat.prime_five (by norm_num) hn5 h5L
      h52 hR)
  obtain ⟨z, hz, hzo⟩ := uc22r3k_exists_mem_centralizer hSg he hL hK hne hset (Or.inr hSz) hp hpq
  have hdvd := u81_dvd_card_centralizer (hBR.trans hR.le) Nat.prime_five (by norm_num)
    (hR.isPGroup.to_le hBR) hpP hp2 hzo (Subgroup.centralizer_le hBX hz)
  have ha5 : a ^ 5 = 1 := by rw [← hao]; exact pow_orderOf_eq_one a
  have hXU : zpowers a ∈ uniqueSet D.M :=
    u81_mem_uniqueSet_of_dvd (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hp)
      hR hBR hBel hΩ (zpowers_le.2 (hΩ a (haR (mem_zpowers a)) ha5)) hNA hdvd
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hao
    omega
  exact uc22r3g_false_of_uniqueSet h1930 c hne hset (uc22r3g_comm_of_isSz hL hSz) hq hq2 hb hbo
    hbT hbL (uc22r3g_not_inner hL (center_eq_bot_of_isSz hL.2.2 hSz) hbL hninn)
    (zpowers_ne_bot.2 ha1) ⟨5, Nat.prime_five, hX5⟩
    (zpowers_le.2 (mem_centralizer_singleton_iff.2 hba.symm)) hXU

@[expose] def S21_22R3F3SzQ5 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ H₁ ∈ hSet D.T D.M, ∀ H₂ ∈ hSet D.T D.M, c.L0 ≤ H₁ ⊓ H₂ →
    (∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G)) →
    ⁅Hinf D.M, oTwoFOf D.M⁆ ≤ CFSG.Open.pCoreOf 2 D.M →
    (∀ p ∈ D.sig, CFSG.Open.pRank p (barPreimage D.M (centE D.M)) = 0) →
    D.sig = D.sig1 → CFSG.Open.evenRank G = 3 →
    ∀ L ∈ calC D.M, (conjSetOf D.M L).ncard = 2 → ∀ n : ℕ, 2 < n → IsSz (Bar2 L) n →
      ∀ (q : ℕ) (b : G), q.Prime → q ∣ n → ¬ q ∣ 2 ^ n - 1 →
        (∃ e m : ℕ, Odd m ∧ c.n = 2 ^ e * m ∧ q ∣ 2 ^ m - 1) →
        b ∈ c.B0 → orderOf b = q → b ∈ normalizer (D.T : Set G) →
        b ∈ normalizer (L : Set G) → n = q → 5 ∉ D.sig → CFSG.Open.pRank 5 D.M = 3 →
        (¬ ∃ y ∈ L, ∀ x ∈ L, b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) → False

theorem s21_22R3F3SzQ_of_s21_22R3F3SzQ5 {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h15 : S21_15C D Ch) (hNN : R847E3ThinNNOut D)
    (h : S21_22R3F3SzQ5 D Ch) : S21_22R3F3SzQ D Ch := by
  intro h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hS1 hU3 hs he L hL hc2 n hn hSz q b hq hqd hqn hm hb hbo
    hbT hbL hnq h5 hninn
  by_cases h3 : 3 ≤ CFSG.Open.pRank 5 D.M
  · refine h h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hS1 hU3 hs he L hL hc2 n hn hSz q b hq hqd hqn hm hb
      hbo hbT hbL hnq h5 (le_antisymm ?_ h3) hninn
    exact (CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 5 Nat.prime_five
      (by norm_num) D.M D.maxLocal.1).trans he.le
  · subst hnq
    obtain ⟨-, m, hmo, -, hqm⟩ := hm
    exact uc22r3k_false_of_le_two hSg h15 hNN h1930 c he hL hc2 hSz hq hqn hmo hqm hb hbo hbT hbL
      hninn h3

end CFSG.LocalAnalysis.UniquenessCase.UC22
