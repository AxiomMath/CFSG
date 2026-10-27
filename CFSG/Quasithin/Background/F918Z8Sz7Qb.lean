module

public import CFSG.Quasithin.Background.F918Z8Sz7Qa
public import CFSG.Quasithin.EmptyFaithful.S153ZA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Count

variable {Y : Type} [CommGroup Y] [Finite Y]

theorem autSec_ne_bot_of_not_le {A : Subgroup (MulAut Y)} {I J : Subgroup Y} (hAI : A ≤ stabSub I)
    (hAJ : A ≤ stabSub J) (hnt : ¬ A ≤ centSec I J) : autSec A I J ≠ ⊥ := by
  intro h
  apply hnt
  have h1 := card_autSec_mul hAI hAJ
  rw [h, Subgroup.card_bot, one_mul] at h1
  exact inf_eq_left.1 (Subgroup.eq_of_le_of_card_ge inf_le_left h1.ge)

theorem rk_autSec_eq_rk_autSub {A : Subgroup (MulAut Y)} {M I J : Subgroup Y}
    (hAM : A ≤ stabSub M) (hAI : A ≤ stabSub I) (hAJ : A ≤ stabSub J)
    (hfaith : A ⊓ centSec I J = A ⊓ centSub M) : rk (autSec A I J) = rk (autSub A M) := by
  have a1 := card_autSec_mul hAI hAJ
  have a2 := card_autSub_mul hAM
  rw [hfaith] at a1
  have := Nat.eq_of_mul_eq_mul_right Nat.card_pos (a1.trans a2.symm)
  unfold rk
  rw [this]

omit [Finite Y] in
theorem commSeries_autSec_eq_bot_of_autSub {A : Subgroup (MulAut Y)} {M I J : Subgroup Y}
    (hIM : I ≤ M) (hAM : A ≤ stabSub M) (hAI : A ≤ stabSub I) {k : ℕ}
    (h : commSeries (autSub A M) k = ⊥) : commSeries (autSec A I J) k = ⊥ := by
  have h1 : commIter M A k = ⊥ := by
    have h2 := map_commIter_autSub hAM k
    have h3 : commIter ⊤ (autSub A M) k = ⊥ := h
    rw [h3, Subgroup.map_bot] at h2
    exact h2.symm
  have h4 : commIter I A k = ⊥ := by
    have h5 : commIter I A k ≤ commIter M A k := commIter_mono hIM le_rfl k
    rw [h1] at h5
    exact le_bot_iff.mp h5
  have h6 : commSeries (autSub A I) k = ⊥ := by
    have h7 := map_commIter_autSub hAI k
    rw [h4] at h7
    exact (Subgroup.map_eq_bot_iff_of_injective _ I.subtype_injective).mp h7
  exact Z391.commSeries_autQuot_eq_bot h6

theorem suz_off_sec_cubicM_proved {A X : Subgroup (MulAut Y)} (hAel : IsElemAbelian2 A)
    {M I J : Subgroup Y} (hJI : J ≤ I) (hIM : I ≤ M) (hAM : A ≤ stabSub M) (hAI : A ≤ stabSub I)
    (hAJ : A ≤ stabSub J) (hcubic : commSeries (autSub A M) 3 = ⊥)
    (hrat : rAV (autSub A M) ≤ ((1 / 2 : ℚ))) (hfaith : A ⊓ centSec I J = A ⊓ centSub M)
    (hnt : ¬ A ≤ centSec I J) :
    qhatOf (autSec (X ⊔ A) I J) ≤ ((1 / 2 : ℚ) : WithTop ℚ) := by
  have hne : autSec A I J ≠ ⊥ := autSec_ne_bot_of_not_le hAI hAJ hnt
  have hA2 : IsA2 (autSec (X ⊔ A) I J) (autSec A I J) :=
    ⟨autSec_mono le_sup_right I J, hne, isElemAbelian2_autSec I J hAel⟩
  refine kq_le_iff.2 ⟨autSec A I J, hA2,
    commSeries_autSec_eq_bot_of_autSub hIM hAM hAI hcubic, ?_⟩
  refine le_trans ?_ hrat
  have hρ := rk_autSec_eq_rk_autSub hAM hAI hAJ hfaith
  have hidx := rkIdx_fixV_autSec_le hJI hIM hAM hAI
  have hpos : 0 < rk (autSec A I J) := hA2.rk_pos
  unfold rAV
  rw [hρ]
  rw [hρ] at hpos
  exact div_le_div_of_nonneg_right (by exact_mod_cast hidx) (by exact_mod_cast hpos.le)

theorem suz_off_sec_proved {A X : Subgroup (MulAut Y)} (hAel : IsElemAbelian2 A)
    {M I J : Subgroup Y} (hJI : J ≤ I) (hIM : I ≤ M) (hAM : A ≤ stabSub M) (hAI : A ≤ stabSub I)
    (hAJ : A ≤ stabSub J) (hcubic : commSeries A 3 = ⊥)
    (hrat : rAV (autSub A M) ≤ ((1 / 2 : ℚ))) (hfaith : A ⊓ centSec I J = A ⊓ centSub M)
    (hnt : ¬ A ≤ centSec I J) :
    qhatOf (autSec (X ⊔ A) I J) ≤ ((1 / 2 : ℚ) : WithTop ℚ) :=
  suz_off_sec_cubicM_proved hAel hJI hIM hAM hAI hAJ (commSeries_autSub_eq_bot hAM hcubic) hrat
    hfaith hnt

end Count

end CFSG.Quasithin
