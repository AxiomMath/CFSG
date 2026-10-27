module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

variable {W : Type} [CommGroup W] [Finite W]

theorem exists_not_commute_of_isIrrOn (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hirr : IsIrrOn L ⊤ ⊥) {t : MulAut W} (ht : orderOf t = 2) :
    ∃ l ∈ L, t * l ≠ l * t := by
  by_contra hne
  push Not at hne
  have hst : StableUnder L (fixV (Subgroup.zpowers t)) := by
    intro l hl u hu
    rw [mem_fixV_zpowers_iff] at hu ⊢
    calc t (l u) = (t * l) u := rfl
      _ = (l * t) u := by rw [hne l hl]
      _ = l (t u) := rfl
      _ = l u := by rw [hu]
  rcases hirr.2.2.2 _ hst bot_le le_top with h0 | h1
  · have hp : IsPGroup 2 (Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    have hmod := card_modEq_card_fixV hp
    rw [h0, Subgroup.card_bot] at hmod
    have hW1 : 1 < Nat.card W := by
      have := (Subgroup.one_lt_card_iff_ne_bot (⊤ : Subgroup W)).2 hirr.1.ne'
      rwa [Subgroup.card_top] at this
    rw [card_eq_two_pow_rk hW] at hmod hW1
    have hr : rk W ≠ 0 := by
      rintro h
      rw [h, pow_zero] at hW1
      omega
    have h2 : 2 ∣ 2 ^ rk W := dvd_pow_self 2 hr
    unfold Nat.ModEq at hmod
    omega
  · have := eq_one_of_fixV_eq_top h1
    rw [this, orderOf_one] at ht
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
