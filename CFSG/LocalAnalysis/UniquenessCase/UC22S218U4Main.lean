module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U4
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Aut
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Out
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U4Out

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem uc22s218n_pRank_le_three_U4 (hGA : GriessAllModelsStatement) (D : Data G)
    (Ch : Choice2011 G) (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h211 : S21_1 D Ch)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hX : IsU4 (BarInf L) n)
    (hn : ¬ IsPowTwo n) {p : ℕ} (hp : p ∈ D.sig) : CFSG.Open.pRank p D.M ≤ 3 := by
  have hZ : Subgroup.center (Bar2 L) = ⊥ := center_bar2_eq_bot_of_isU4 hGA hL hX hn
  refine uc22s218n_pRank_le_three_of_facts_ex D Ch hSg h614 h211 h76 hH c hL (torusFacts218_U4 hX)
    (fun ℓ hℓ hdvd => ?_) hn hp ?_
  · rw [hZ, Subgroup.card_bot] at hdvd
    exact absurd hdvd hℓ.not_dvd_one
  · intro hT hO h4 hN s r hs hsn hr hrs hrK
    have := hN
    obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
    have hLM : L ≤ D.M := hL.1.le
    have hp1 : p ∣ 2 ^ n + 1 := by
      by_contra h
      exact hO ⟨hT, h⟩
    have hp2n : p ∣ 2 ^ (2 * n) - 1 := by
      have h1 : 2 ^ (2 * n) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
        have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        have h3 : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
        rw [h3]
        zify [h2, Nat.one_le_pow 2 (2 ^ n) (by omega)]
        ring
      rw [h1]
      exact Dvd.dvd.mul_left hp1 _
    have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
    have hpr : p ≠ r := by
      rintro rfl
      exact hT (hrn)
    have hpK : ¬ p ∣ Nat.card (CFSG.solvableRadical ↥L) :=
      not_dvd_card_solvableRadical hL.2.2 hpp hp2 (fun h => by
        rw [hZ, Subgroup.card_bot] at h
        exact hpp.not_dvd_one h)
    obtain ⟨T, hTc, hTE, hTo⟩ := uc22s218_u4_torus hX
    obtain ⟨E₀, hE₀T, hE₀, hE₀c⟩ := hTE r hr hrn
    obtain ⟨y, hyT, hyo⟩ := hTo p hpp hp2n
    refine uc22s218_exists_pair_of_outer hLM (CFSG.solvableRadical ↥L) hpp hr hpr hpK hrK h4
      hE₀ hE₀c hyo (fun e he => hTc y hyT e (hE₀T he)) ?_
      (fun V hV hVc => uc22s218_u4_outer_pair hX hpp hp2 hp1 hr hrn V hV hVc)
    by_contra hcen
    have hy1 := (uc22s218_u4_fieldBorel hX).center_eq_one y fun x =>
      (by_contra fun h => hcen ⟨x, h⟩ : x * y = y * x).symm
    rw [hy1, orderOf_one] at hyo
    exact hpp.one_lt.ne hyo

end CFSG.LocalAnalysis.UniquenessCase.UC22
