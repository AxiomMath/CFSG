module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightCaseTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightTheta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtySevenPrelim

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem exists_order_three_fixed {K : Subgroup G} {b : G}
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) {s : ℕ} {x : xbar K}
    (hse : s = 1 ∨ Even s)
    (hs1 : s = 1 → ∃ z : xbar K, orderOf z = 3 ∧ inducedQuotInfAut K b hbN z = z)
    (hxord : orderOf x = 2 ^ s - 1)
    (hxfix : inducedQuotInfAut K b hbN x = x) :
    ∃ z : xbar K, orderOf z = 3 ∧ inducedQuotInfAut K b hbN z = z := by
  rcases hse with h1 | hev
  · exact hs1 h1
  · obtain ⟨k, rfl⟩ := hev
    have hdvd3 : 3 ∣ 2 ^ (k + k) - 1 := by
      have hpow : 2 ^ (k + k) = 4 ^ k := by
        rw [show k + k = 2 * k by omega, pow_mul]
        norm_num
      rw [hpow]
      simpa using Nat.sub_one_dvd_pow_sub_one 4 k
    have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
    refine ⟨x ^ ((2 ^ (k + k) - 1) / 3), ?_, ?_⟩
    · have h := orderOf_pow_orderOf_div (x := x) hx0 (n := 3) (by rw [hxord]; exact hdvd3)
      simpa [hxord] using h
    · rw [map_pow, hxfix]

private theorem false_of_three_dvd_card_of_ne {D : Data G} {Ch : Choice2011 G}
    (h54 : S23_5_4 D Ch) (h8107 : F08.R8107 D) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {K K' : Subgroup G} (hK : K ∈ calC D.M) (hK' : K' ∈ calC D.M) (hne : K' ≠ K)
    (hthinK : F08.Thin8 K) (hthinK' : F08.Thin8 K') (h3K' : 3 ∣ Nat.card K')
    {b : G} (hb : b ∈ c.B0) (hbZ : b ∉ Subgroup.centralizer (D.Z : Set G))
    {A : Subgroup G} (hAK : A ≤ K) (hAcard : Nat.card A = 3)
    (hAM : A ≤ D.M) (hAC : A ≤ Subgroup.centralizer ({b} : Set G)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrankK : CFSG.Open.pRank 3 K = 1 := by
    refine le_antisymm (hthinK 3 Nat.prime_three (by norm_num)) ?_
    exact CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hAK
      (CFSG.GroupTheory.isElemAbelian_of_card_prime hAcard) (by rw [hAcard, pow_one])
  obtain ⟨y', hy'ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥K') 3 h3K'
  let A' : Subgroup G := Subgroup.zpowers ((y' : ↥K') : G)
  have hA'K' : A' ≤ K' := Subgroup.zpowers_le.mpr y'.2
  have hA'card : Nat.card A' = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy'ord]
  have hrankK' : CFSG.Open.pRank 3 K' = 1 := by
    refine le_antisymm (hthinK' 3 Nat.prime_three (by norm_num)) ?_
    exact CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hA'K'
      (CFSG.GroupTheory.isElemAbelian_of_card_prime hA'card) (by rw [hA'card, pow_one])
  have huniq := (h8107 K hK K' hK' hne.symm hrankK hrankK' (Or.inl hthinK) (Or.inl hthinK')
    A A' hAK hAcard hA'K' hA'card).1
  have hAne : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hAcard
    omega
  have hpgrp : IsPGroup 3 ↥A := IsPGroup.iff_card.mpr ⟨1, by simpa using hAcard⟩
  exact ((h54 h1930 c.withB0 b (by simpa using hb) hbZ).2 3 Nat.prime_three A hAne hpgrp
    (le_inf hAM hAC)).1 huniq

private theorem normal_and_barImage_of_caseA {D : Data G} {Ch : Choice2011 G}
    (hI : ∀ K' ∈ calC D.M, ∀ a : ℕ, ¬ (Odd a ∧ IsSp4 (Bar2 K') a) ∧ ¬ IsSU3 (Bar2 K') a)
    (h2116 : S21_16 D Ch) (h54 : S23_5_4 D Ch) (h8107 : F08.R8107 D)
    (h1930 : H1930 D) (c : Ctx23L D Ch) {K : Subgroup G}
    (hK : K ∈ calC D.M) {a : ℕ} (hL2 : IsL2 (Bar2 K) a) {b : G} (hb : b ∈ c.B0)
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) (hbodd : Odd (orderOf b))
    (hbZ : b ∉ Subgroup.centralizer (D.Z : Set G)) {x3 : xbar K} (hx3 : orderOf x3 = 3)
    (hfix3 : inducedQuotInfAut K b hbN x3 = x3) :
    (K.subgroupOf D.M).Normal ∧ barImage D.M K = Opp 3 (CFSG.layer (Bar2 D.M)) := by
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  have hc : Subgroup.center (Bar2 K) = ⊥ := center_eq_bot_of_isL2 hq hL2
  have hrZ : ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 K)) := by simp [hc]
  obtain ⟨y, hyC, hyord, -⟩ :=
    exists_mem_centralizer_of_quotInf_fixed hK hbN hbodd Nat.prime_three (by norm_num) hrZ
      hx3 hfix3
  let A : Subgroup G := Subgroup.zpowers (y : G)
  have hAcard : Nat.card A = 3 := by
    change Nat.card (Subgroup.zpowers (y : G)) = 3
    rw [Nat.card_zpowers, hyord]
  have hAK : A ≤ K := Subgroup.zpowers_le.mpr y.2
  have hAM : A ≤ D.M := hAK.trans hK.1.le
  have hAC : A ≤ Subgroup.centralizer ({b} : Set G) := Subgroup.zpowers_le.mpr hyC
  have hthinK : F08.Thin8 K := thin8_of_isL2_or_isSz (Or.inl hL2)
  have hother : ∀ K' ∈ calC D.M, K' ≠ K → ¬ 3 ∣ Nat.card K' := by
    intro K' hK' hne h3K'
    rcases Ctx23L.isL2_or_isL2Odd_or_isJ1_of_three_dvd_card hI h2116 h1930 c hK' h3K' with
      ⟨n, hL2'⟩ | ⟨p, hp, hp2, hL2Odd⟩ | hJ1
    · exact false_of_three_dvd_card_of_ne h54 h8107 h1930 c hK hK' hne hthinK
        (thin8_of_isL2_or_isSz (Or.inl hL2')) h3K' hb hbZ hAK hAcard hAM hAC
    · exact false_of_three_dvd_card_of_ne h54 h8107 h1930 c hK hK' hne hthinK
        (thin8_of_isL2Odd_bar2 hp hp2 hL2Odd) h3K' hb hbZ hAK hAcard hAM hAC
    · exact false_of_three_dvd_card_of_ne h54 h8107 h1930 c hK hK' hne hthinK
        (thin8_of_isJ1_bar2 hJ1) h3K' hb hbZ hAK hAcard hAM hAC
  have h3bar : 3 ∣ Nat.card (Bar2 K ⧸ Subgroup.center (Bar2 K)) := by
    rw [uc22p21k_card_quot_center hc]
    exact three_dvd_card_of_isL2 hL2
  have hbar := barImage_eq_opp_three_layer hK hother h3bar
  exact ⟨normal_of_barImage_eq_opp_layer hK hbar, hbar⟩

theorem Ctx23L.normal_of_isL2 {D : Data G} {Ch : Choice2011 G}
    (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h52 : S23_5_2 D Ch) (h53 : S23_5_3 D Ch)
    (h54 : S23_5_4 D Ch) (h215 : S21_5 D Ch) (h2115 : S21_15N D Ch) (h2116 : S21_16 D Ch)
    (h8107 : F08.R8107 D) (hBor : KBor) (hCent : KCentL2)
    (hsig : D.sig.Nonempty) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hI : ∀ K' ∈ calC D.M, ∀ a : ℕ, ¬ (Odd a ∧ IsSp4 (Bar2 K') a) ∧ ¬ IsSU3 (Bar2 K') a)
    {K : Subgroup G} (hK : K ∈ calC D.M) {a : ℕ} (hL2 : IsL2 (Bar2 K) a) :
    (K.subgroupOf D.M).Normal ∧
      (Odd a ∨ barImage D.M K = Opp 3 (CFSG.layer (Bar2 D.M))) := by
  classical
  obtain ⟨hm2, -⟩ := c.exists_mem_B0_not_mem_centralizer_Z hE h207 h52 h53 h1930
  have h4 : 4 ≤ 2 ^ CFSG.Open.pRank 2 D.Z := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 D.Z := Nat.pow_le_pow_right (by norm_num) hm2
  have hne : 2 ^ CFSG.Open.pRank 2 D.Z - 1 ≠ 1 := by omega
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hne
  obtain ⟨b, hb0, hbN, hbodd, hbZ, hθodd, S, hScoe, hSinv, hforbid⟩ :=
    exists_thetaData hE h207 h52 h53 h54 h215 hBor h1930 c hK (Or.inl hL2) hr hrdvd
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  have hc : Subgroup.center (Bar2 K) = ⊥ := center_eq_bot_of_isL2 hq hL2
  have hL2x : IsL2 (xbar K) a := lieModel_xbar_of_lieModel_bar2 hq hc hL2
  obtain ⟨s, hsdvd, hsodd_div, ⟨x, hxord, hxfix⟩, hs1⟩ :=
    hCent (xbar K) a hL2x (inducedQuotInfAut K b hbN) hθodd S hSinv
  rcases Nat.even_or_odd s with hse | hso
  · obtain ⟨x3, hx3, hfix3⟩ := exists_order_three_fixed hbN (Or.inr hse) hs1 hxord hxfix
    obtain ⟨hnorm, hbar⟩ := normal_and_barImage_of_caseA hI h2116 h54 h8107 h1930 c
      hK hL2 hb0 hbN hbodd hbZ hx3 hfix3
    exact ⟨hnorm, Or.inr hbar⟩
  · rcases eq_or_ne s 1 with hsone | hsne
    · obtain ⟨x3, hx3, hfix3⟩ := hs1 hsone
      obtain ⟨hnorm, hbar⟩ := normal_and_barImage_of_caseA hI h2116 h54 h8107 h1930 c
        hK hL2 hb0 hbN hbodd hbZ hx3 hfix3
      exact ⟨hnorm, Or.inr hbar⟩
    · have hnorm := normal_of_caseB h2115 h54 hsig h1930 c hK (Or.inl hL2) hb0 hbN hbodd hbZ
        hsdvd hso hsne hxord hxfix
      have haodd : Odd a := by
        have h : a = s * (a / s) := (Nat.mul_div_cancel' hsdvd).symm
        rw [h]
        exact hso.mul hsodd_div
      exact ⟨hnorm, Or.inl haodd⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
