module

public import CFSG.GH74.Generic.GKFTables
public import CFSG.GH74.Generic.GKFBridge
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.GH74.Generic.Certificates

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG CFSG.Blueprint CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover
open CFSG.GH74.Generic (card_hopfMultiplier_of_griess card_center_dvd_hopfMultiplier models_of_blueprint_of_ne_zero)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.CGT.PushingUpLit.CGT6 (SporadicThreeCenterSmallPrimes)

section Orders

theorem exceptionalOrders_psl2 (p f : ℕ) : exceptionalOrders .PSL 2 p f = (2, 1) ∨
    exceptionalOrders .PSL 2 p f = (3, 1) ∨ exceptionalOrders .PSL 2 p f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all

theorem exceptionalOrders_psl3 {p f : ℕ} (hq : p ^ f % 3 = 2) :
    exceptionalOrders .PSL 3 p f = (2, 1) ∨ exceptionalOrders .PSL 3 p f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all

theorem exceptionalOrders_psu3 (p f : ℕ) : exceptionalOrders .PSU 3 p f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all

variable {X : Type} [Group X] {p f : ℕ}

theorem card_hopfMultiplier_psl2_dvd (hGA : GriessMultipliersAllModels)
    (hm : CFSG.Models.LieModel X .PSL 2 p f) : Nat.card (hopfMultiplier X) ∣ 12 := by
  rw [card_hopfMultiplier_of_griess hGA hm]
  have hgen : genericOrders .PSL 2 p f = (Nat.gcd 2 (p ^ f - 1), 1) := rfl
  have hg : Nat.gcd 2 (p ^ f - 1) ∣ 2 := Nat.gcd_dvd_left _ _
  rw [hgen]
  rcases (Nat.dvd_prime Nat.prime_two).1 hg with h1 | h1 <;> rcases exceptionalOrders_psl2 p f with h | h | h <;>
    simp [h, h1]

theorem card_hopfMultiplier_psl3_dvd (hGA : GriessMultipliersAllModels)
    (hm : CFSG.Models.LieModel X .PSL 3 p f) (hq : p ^ f % 3 = 2) : Nat.card (hopfMultiplier X) ∣ 12 := by
  rw [card_hopfMultiplier_of_griess hGA hm]
  have hcop : Nat.gcd 3 (p ^ f - 1) = 1 := by
    have : ¬ 3 ∣ p ^ f - 1 := by omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 this
  have hgen : genericOrders .PSL 3 p f = (Nat.gcd 3 (p ^ f - 1), 1) := rfl
  rw [hgen, hcop]
  rcases exceptionalOrders_psl3 hq with h | h <;> simp [h]

theorem card_hopfMultiplier_psu3_dvd (hGA : GriessMultipliersAllModels)
    (hm : CFSG.Models.LieModel X .PSU 3 p f) (hq : p ^ f % 3 = 1) : Nat.card (hopfMultiplier X) ∣ 12 := by
  rw [card_hopfMultiplier_of_griess hGA hm]
  have hcop : Nat.gcd 3 (p ^ f + 1) = 1 := by
    have : ¬ 3 ∣ p ^ f + 1 := by omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 this
  have hgen : genericOrders .PSU 3 p f = (Nat.gcd 3 (p ^ f + 1), 1) := rfl
  rw [hgen, hcop, exceptionalOrders_psu3]
  norm_num

end Orders

theorem center_eq_bot_of_card_dvd_twelve {G : Type} [Group G] [Finite G] {N : ℕ} (hN : N ∣ 12)
    (hZN : Nat.card (Subgroup.center G) ∣ N) (hodd : Odd (Nat.card (Subgroup.center G)))
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center G)) : Subgroup.center G = ⊥ := by
  have h2 : ¬ 2 ∣ Nat.card (Subgroup.center G) := by
    have := Nat.odd_iff.1 hodd
    omega
  have hc2 : Nat.Coprime (Nat.card (Subgroup.center G)) 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2).symm
  have hc3 : Nat.Coprime (Nat.card (Subgroup.center G)) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
  have hc12 : Nat.Coprime (Nat.card (Subgroup.center G)) 12 := by
    have : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
    rw [this]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right 2 hc2) hc3
  have h1 : Nat.card (Subgroup.center G) = 1 := Nat.Coprime.eq_one_of_dvd hc12 (hZN.trans hN)
  exact Subgroup.card_eq_one.1 h1

theorem center_eq_bot_of_catalog (hGA : GriessMultipliersAllModels) (hSp : SporadicThreeCenterSmallPrimes)
    {G : Type} [Group G] [Finite G] (hqs : CFSG.IsQuasisimple G)
    (hodd : Odd (Nat.card (Subgroup.center G))) (h3 : ¬ 3 ∣ Nat.card (Subgroup.center G))
    (hL : (∃ p f : ℕ, LieModel (G ⧸ Subgroup.center G) .PSL 2 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel (G ⧸ Subgroup.center G) .PSL 3 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel (G ⧸ Subgroup.center G) .PSU 3 p f) ∨
      UC22.IsSpor (G ⧸ Subgroup.center G) .J1) : Subgroup.center G = ⊥ := by
  have hdvd := card_center_dvd_hopfMultiplier hqs (MulEquiv.refl (G ⧸ Subgroup.center G))
  rcases hL with ⟨p, f, hm⟩ | ⟨p, f, hq, hm⟩ | ⟨p, f, hq, hm⟩ | hJ
  · exact center_eq_bot_of_card_dvd_twelve
      (card_hopfMultiplier_psl2_dvd hGA (models_of_blueprint_of_ne_zero (by norm_num) hm)) hdvd hodd h3
  · exact center_eq_bot_of_card_dvd_twelve
      (card_hopfMultiplier_psl3_dvd hGA (models_of_blueprint_of_ne_zero (by norm_num) hm) hq) hdvd hodd h3
  · exact center_eq_bot_of_card_dvd_twelve
      (card_hopfMultiplier_psu3_dvd hGA (models_of_blueprint_of_ne_zero (by norm_num) hm) hq) hdvd hodd h3
  · by_contra hne
    have h1 : Nat.card (Subgroup.center G) ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
    obtain ⟨r, hr, hrZ⟩ := Nat.exists_prime_and_dvd h1
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hrZ)
    have hr3 : r ≠ 3 := by
      rintro rfl
      exact h3 hrZ
    have hr4 : 3 < r := by
      have := hr.two_le
      omega
    exact hSp G hqs (Or.inr (Or.inl hJ)) r hr hr4 hrZ

end CFSG.LocalAnalysis.UniquenessCase.UCK
