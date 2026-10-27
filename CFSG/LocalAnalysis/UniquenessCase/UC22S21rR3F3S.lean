module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3F3B
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3F3A
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4Exc
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22r3g_false_of_five {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h1930 : H1930 D) (c : Ctx21 D Ch) (hs : D.sig = D.sig1)
    (h5 : 5 ∈ D.sig) {L : Subgroup G} (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2)
    {n : ℕ} (hSz : IsSz (Bar2 L) n) {q m : ℕ} {b : G} (hq : q.Prime) (hqn : ¬ q ∣ 2 ^ n - 1)
    (hm : Odd m) (hqm : q ∣ 2 ^ m - 1) (hb : b ∈ c.B0) (hbo : orderOf b = q)
    (hbT : b ∈ normalizer (D.T : Set G)) (hbL : b ∈ normalizer (L : Set G))
    (hninn : ¬ ∃ y ∈ L, ∀ x ∈ L, b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) :
    False := by
  obtain ⟨K, hne, hset, -⟩ := uc22s21ru4e_exists_second_member hc2 hL
  have hq7 := PartTwo.s13_seven_le_of_dvd hm hq hqm
  have hq2 : q ≠ 2 := by omega
  obtain ⟨a, haL, hao, hba⟩ := uc22r3g_exists_commute (by norm_num : Nat.Prime 5) hq hbo hbL
    (uc22r3g_not_dvd_card (Or.inr hSz) hq hq2 hqn hm hqm) (uc22r3g_five_dvd_card hSz)
    (PartTwo.S17.thin8_of_isSz hSz 5 (by norm_num) (by norm_num)) (by omega)
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hao
    omega
  have hX5 : IsPGroup 5 ↥(zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao, pow_one])
  have hXU : zpowers a ∈ uniqueSet D.M :=
    mem_uniqueSet_of_isStronglyPEmbedded (by norm_num) (hSg.sig1_sp 5 (by rw [← hs]; exact h5))
      ((zpowers_le.2 haL).trans hL.1.le) (zpowers_ne_bot.2 ha1) hX5
  exact uc22r3g_false_of_uniqueSet h1930 c hne hset (uc22r3g_comm_of_isSz hL hSz) hq hq2 hb hbo
    hbT hbL (uc22r3g_not_inner hL (center_eq_bot_of_isSz hL.2.2 hSz) hbL hninn)
    (zpowers_ne_bot.2 ha1) ⟨5, by norm_num, hX5⟩
    (zpowers_le.2 (mem_centralizer_singleton_iff.2 hba.symm)) hXU

@[expose] def S21_22R3F3SzQ (D : Data G) (Ch : Choice2011 G) : Prop :=
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
        b ∈ normalizer (L : Set G) → n = q → 5 ∉ D.sig →
        (¬ ∃ y ∈ L, ∀ x ∈ L, b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) → False

theorem s21_22R3F3Sz_of {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h15 : S21_15C D Ch) (hU2 : R8100U2 D)
    (hSzQ : S21_22R3F3SzQ D Ch) : S21_22R3F3Sz D Ch := by
  intro h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hS1 hU3 hs he L hL hc2 n hn hSz q b hq hqd hqn hm hb hbo
    hbT hbL hninn
  by_cases h5 : 5 ∈ D.sig
  · obtain ⟨-, m, hmo, -, hqm⟩ := hm
    exact uc22r3g_false_of_five hSg h1930 c hs h5 hL hc2 hSz hq hqn hmo hqm hb hbo hbT hbL hninn
  by_cases hnq : n = q
  · exact hSzQ h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hS1 hU3 hs he L hL hc2 n hn hSz q b hq hqd hqn hm hb
      hbo hbT hbL hnq h5 hninn
  · obtain ⟨-, m, hmo, -, hqm⟩ := hm
    exact uc22r3g_false_of_ne hSg h15 hU2 h1930 c he hL hc2 hSz hq hqn hmo hqm hnq hb hbo hbT hbL
      hninn

theorem s21_22R3F3_of {D : Data G} {Ch : Choice2011 G}
    (h8107 : F08.R8107 D) (hSg : UC6S846.SigmaStd D) (h15 : S21_15C D Ch) (hU2 : R8100U2 D)
    (hSzQ : S21_22R3F3SzQ D Ch) : S21_22R3F3 D Ch :=
  s21_22R3F3_of_sz h8107 (s21_22R3F3Sz_of hSg h15 hU2 hSzQ)

end CFSG.LocalAnalysis.UniquenessCase.UC22
