module

public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.Quasithin

variable {W : Type} [CommGroup W] [Finite W]

theorem rkIdx_inf_le_add (A B : Subgroup W) : rkIdx (A ⊓ B) ≤ rkIdx A + rkIdx B := by
  have h1 := rk_sup_add_rk_inf A B
  have h2 : rk ↥(A ⊔ B) ≤ rk W := by
    have := rk_mono (le_top : A ⊔ B ≤ ⊤)
    rwa [rk_top] at this
  have h3 := rk_add_rkIdx A
  have h4 := rk_add_rkIdx B
  have h5 := rk_add_rkIdx (A ⊓ B)
  omega

theorem orderOf_two_dvd_rkIdx_fixV (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) {y : MulAut W} (hy : orderOf y = p) :
    orderOf (2 : ZMod p) ∣ rkIdx (fixV (Subgroup.zpowers y)) := by
  have hP : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have hmod := card_modEq_card_fixV hP
  have hsum := rk_add_rkIdx (fixV (Subgroup.zpowers y))
  rw [card_eq_two_pow_rk hW, card_eq_two_pow hW (fixV (Subgroup.zpowers y)), ← hsum,
    pow_add] at hmod
  have h3 := (ZMod.natCast_eq_natCast_iff _ _ p).2 hmod
  push_cast at h3
  have hne : (2 : ZMod p) ^ rk ↥(fixV (Subgroup.zpowers y)) ≠ 0 := pow_ne_zero _ h2
  have h4 : (2 : ZMod p) ^ rkIdx (fixV (Subgroup.zpowers y)) = 1 :=
    mul_left_cancel₀ hne (h3.trans (mul_one _).symm)
  exact orderOf_dvd_of_pow_eq_one h4

end CFSG.Quasithin
