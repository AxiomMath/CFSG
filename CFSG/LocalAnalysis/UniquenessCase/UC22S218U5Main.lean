module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem uc22s218n_pRank_le_three_U5 (hGA : GriessAllModelsStatement) (D : Data G)
    (Ch : Choice2011 G) (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h211 : S21_1 D Ch)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hX : IsU5 (BarInf L) n)
    (hn : ¬ IsPowTwo n) {p : ℕ} (hp : p ∈ D.sig) (hgen : ¬ (p = 5 ∧ 5 ∣ 2 ^ n + 1)) :
    CFSG.Open.pRank p D.M ≤ 3 := by
  refine uc22s218n_pRank_le_three_of_facts D Ch hSg h614 h211 h76 hH c hL (torusFacts218_U5 hX)
    (fun ℓ hℓ hdvd => ?_) hn hp ?_
  ·
    have h1 : ℓ ∣ Nat.gcd 5 (2 ^ n + 1) := hdvd.trans (card_center_bar2_dvd_of_isU5 hGA hL hX)
    have hℓ5 : ℓ = 5 :=
      (Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).1 (h1.trans (Nat.gcd_dvd_left _ _))
    have h5n : 5 ∣ 2 ^ n + 1 := hℓ5 ▸ h1.trans (Nat.gcd_dvd_right _ _)
    subst hℓ5
    have hq : 2 ^ n + 1 ∣ 2 ^ (2 * n) - 1 := by
      have hfac : 2 ^ (2 * n) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
        have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        have e : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
        rw [e]
        generalize 2 ^ n = x at h ⊢
        have h3 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ h
        zify [h, h3]
        ring
      exact Dvd.intro_left _ hfac.symm
    exact ⟨fun h => h.2 ⟨rfl, h5n⟩, fun h => h (h5n.trans hq)⟩
  · by_cases h : p ∣ 2 ^ (2 * n) - 1
    · exact Or.inl ⟨h, hgen⟩
    · exact Or.inr h

end CFSG.LocalAnalysis.UniquenessCase.UC22
