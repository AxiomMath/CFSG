module

public import CFSG.RankThree.PartOne.KF.ClsCenter
public import CFSG.RankThree.PartOne.Q1327T.Defs
public import CFSG.RankThree.PartOne.S15K.JointEigen

public section

namespace CFSG.RankThree.PartOne.Q1327F

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Q1327T
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)

theorem center_eq_bot_of_multiplier' {p ℓ : ℕ} (hp : p.Prime)
    (hGA : CFSG.Open.GriessAllModelsStatement) {Q : Type}
    [Group Q] [Finite Q] (hqs : CFSG.IsQuasisimple Q) (hZ : IsPGroup p (Subgroup.center Q))
    {t : StatedLieTag} {n f : ℕ} (hm : Models.LieModel (Q ⧸ Subgroup.center Q) t n ℓ f)
    (hcop : ¬ p ∣ Nat.card (Blueprint.Multiplier.generic t n ℓ f ×
      Blueprint.Multiplier.exceptional t n ℓ f)) : Subgroup.center Q = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hperfT, hcard⟩ := card_hopfMultiplier_of_model hGA hm
  have hdvd := card_ker_dvd_card_hopfMultiplier hperfT hqs.1 (QuotientGroup.mk' (Subgroup.center Q))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le
  rw [hcard, QuotientGroup.ker_mk'] at hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hZ
  rw [← Subgroup.card_eq_one]
  rw [hk] at hdvd ⊢
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0, pow_zero]
  · exact absurd ((dvd_pow_self p hpos.ne').trans hdvd) hcop

theorem not_dvd_thirtySix {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ 36 := fun hd => by
  have h : p ∣ 2 ^ 2 * 3 ^ 2 := by simpa using hd
  rcases hp.dvd_mul.1 h with h2 | h3
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
    omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
    omega

theorem card_generic_exceptional (t : StatedLieTag) (n p f : ℕ)
    (h1 : (Blueprint.Multiplier.genericOrders t n p f).1 ≠ 0)
    (h2 : (Blueprint.Multiplier.genericOrders t n p f).2 ≠ 0)
    (h3 : (Blueprint.Multiplier.exceptionalOrders t n p f).1 ≠ 0)
    (h4 : (Blueprint.Multiplier.exceptionalOrders t n p f).2 ≠ 0) :
    Nat.card (Blueprint.Multiplier.generic t n p f × Blueprint.Multiplier.exceptional t n p f) =
      ((Blueprint.Multiplier.genericOrders t n p f).1 *
        (Blueprint.Multiplier.genericOrders t n p f).2) *
      ((Blueprint.Multiplier.exceptionalOrders t n p f).1 *
        (Blueprint.Multiplier.exceptionalOrders t n p f).2) := by
  have : NeZero (Blueprint.Multiplier.genericOrders t n p f).1 := ⟨h1⟩
  have : NeZero (Blueprint.Multiplier.genericOrders t n p f).2 := ⟨h2⟩
  have : NeZero (Blueprint.Multiplier.exceptionalOrders t n p f).1 := ⟨h3⟩
  have : NeZero (Blueprint.Multiplier.exceptionalOrders t n p f).2 := ⟨h4⟩
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem card_multiplier_psl_four_dvd {r f : ℕ} (hr : r ≠ 2) :
    Nat.card (Blueprint.Multiplier.generic .PSL 4 r f ×
      Blueprint.Multiplier.exceptional .PSL 4 r f) ∣ 36 := by
  have hgen : Blueprint.Multiplier.genericOrders .PSL 4 r f = (Nat.gcd 4 (r ^ f - 1), 1) := rfl
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSL 4 r f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  have hg0 : Nat.gcd 4 (r ^ f - 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  rw [card_generic_exceptional _ _ _ _ (by rw [hgen]; exact hg0) (by rw [hgen]; norm_num)
    (by rw [hexc]; norm_num) (by rw [hexc]; norm_num), hgen, hexc]
  simp only [mul_one]
  exact (Nat.gcd_dvd_left 4 _).trans (by norm_num)

theorem card_multiplier_psu_four_dvd {r f : ℕ} (hr : r ≠ 2) :
    Nat.card (Blueprint.Multiplier.generic .PSU 4 r f ×
      Blueprint.Multiplier.exceptional .PSU 4 r f) ∣ 36 := by
  have hgen : Blueprint.Multiplier.genericOrders .PSU 4 r f = (Nat.gcd 4 (r ^ f + 1), 1) := rfl
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSU 4 r f = (1, 1) ∨
      Blueprint.Multiplier.exceptionalOrders .PSU 4 r f = (3, 3) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  have hg0 : Nat.gcd 4 (r ^ f + 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  have hg4 : Nat.gcd 4 (r ^ f + 1) ∣ 4 := Nat.gcd_dvd_left 4 _
  rcases hexc with hexc | hexc
  · rw [card_generic_exceptional _ _ _ _ (by rw [hgen]; exact hg0) (by rw [hgen]; norm_num)
      (by rw [hexc]; norm_num) (by rw [hexc]; norm_num), hgen, hexc]
    simp only [mul_one]
    exact hg4.trans (by norm_num)
  · rw [card_generic_exceptional _ _ _ _ (by rw [hgen]; exact hg0) (by rw [hgen]; norm_num)
      (by rw [hexc]; norm_num) (by rw [hexc]; norm_num), hgen, hexc]
    simp only [mul_one]
    exact (Nat.mul_dvd_mul hg4 (dvd_refl 9)).trans (by norm_num)

theorem card_multiplier_psp_two_dvd {r f : ℕ} (hr : r ≠ 2) :
    Nat.card (Blueprint.Multiplier.generic .PSp 2 r f ×
      Blueprint.Multiplier.exceptional .PSp 2 r f) ∣ 36 := by
  have hgen : Blueprint.Multiplier.genericOrders .PSp 2 r f = (Nat.gcd 2 (r ^ f - 1), 1) := rfl
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSp 2 r f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  have hg0 : Nat.gcd 2 (r ^ f - 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  rw [card_generic_exceptional _ _ _ _ (by rw [hgen]; exact hg0) (by rw [hgen]; norm_num)
    (by rw [hexc]; norm_num) (by rw [hexc]; norm_num), hgen, hexc]
  simp only [mul_one]
  exact (Nat.gcd_dvd_left 2 _).trans (by norm_num)

theorem card_multiplier_g2_dvd {r f : ℕ} (hr : r ≠ 2) :
    Nat.card (Blueprint.Multiplier.generic .G2 0 r f ×
      Blueprint.Multiplier.exceptional .G2 0 r f) ∣ 36 := by
  have hgen : Blueprint.Multiplier.genericOrders .G2 0 r f = (1, 1) := rfl
  have hexc : Blueprint.Multiplier.exceptionalOrders .G2 0 r f = (1, 1) ∨
      Blueprint.Multiplier.exceptionalOrders .G2 0 r f = (3, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  rcases hexc with hexc | hexc
  · rw [card_generic_exceptional _ _ _ _ (by rw [hgen]; norm_num) (by rw [hgen]; norm_num)
      (by rw [hexc]; norm_num) (by rw [hexc]; norm_num), hgen, hexc]
    norm_num
  · rw [card_generic_exceptional _ _ _ _ (by rw [hgen]; norm_num) (by rw [hgen]; norm_num)
      (by rw [hexc]; norm_num) (by rw [hexc]; norm_num), hgen, hexc]
    norm_num

end CFSG.RankThree.PartOne.Q1327F
