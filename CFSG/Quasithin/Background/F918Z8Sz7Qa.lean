module

public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.Quasithin.Background.D2Offenders

public section

namespace CFSG.Quasithin

section Count

variable {Y : Type} [CommGroup Y] [Finite Y]

theorem rAV_quarter_proved {A : Subgroup (MulAut Y)} {W M : Subgroup Y} (hAW : A ≤ stabSub W)
    (hAM : A ≤ stabSub M) (hW : Nat.card ↥W = Nat.card ↥M ^ 4)
    (hC : Nat.card ↥(W ⊓ fixV A) = Nat.card ↥(M ⊓ fixV A) ^ 4)
    (hker : A ⊓ centSub M = A ⊓ centSub W) :
    rAV (autSub A M) * 4 = rAV (autSub A W) := by
  have h1 := rkIdx_autSub_add hAW
  have h2 := rkIdx_autSub_add hAM
  have hrW : rk ↥W = 4 * rk ↥M := by
    unfold rk
    rw [hW, padicValNat.pow]
  have hrC : rk ↥(W ⊓ fixV A) = 4 * rk ↥(M ⊓ fixV A) := by
    unfold rk
    rw [hC, padicValNat.pow]
  have hidx : rkIdx (fixV (autSub A W)) = 4 * rkIdx (fixV (autSub A M)) := by omega
  have hrk : rk (autSub A W) = rk (autSub A M) := by
    have a1 := rk_autSub_add_rk_inf hAW
    have a2 := rk_autSub_add_rk_inf hAM
    rw [hker] at a2
    omega
  unfold rAV
  rw [hrk, hidx]
  push_cast
  ring

end Count

section Sections

variable {V : Type*} [CommGroup V] [Finite V]

theorem rk_fixV_le_autQuot_gen {A : Subgroup (MulAut V)} {U : Subgroup V} :
    rk (fixV A) ≤ rk (fixV (autQuot A U)) + rk ↥(U ⊓ fixV A) := by
  have h1 := B1More.card_map_mul_card_inf_ker (fixV A) (QuotientGroup.mk' U)
  have h2 : (fixV A).map (QuotientGroup.mk' U) ≤ fixV (autQuot A U) := by
    rintro _ ⟨v, hv, rfl⟩
    exact mk_mem_fixV_autQuot.2 fun g hg _ => by rw [hv g hg]; simp
  have h3 : fixV A ⊓ (QuotientGroup.mk' U).ker = U ⊓ fixV A := by
    rw [QuotientGroup.ker_mk', inf_comm]
  rw [h3] at h1
  have h4 : Nat.card ↥((fixV A).map (QuotientGroup.mk' U)) ∣ Nat.card (fixV (autQuot A U)) :=
    Subgroup.card_dvd_of_le h2
  have h5 := padicValNat_two_le_of_dvd Nat.card_pos.ne' h4
  unfold rk
  rw [← h1, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne']
  exact Nat.add_le_add_right h5 _

theorem rk_inf_fixV_le_autSec_gen {A : Subgroup (MulAut V)} {W U : Subgroup V} (hUW : U ≤ W)
    (hAW : A ≤ stabSub W) :
    rk ↥(W ⊓ fixV A) ≤ rk (fixV (autSec A W U)) + rk ↥(U ⊓ fixV A) := by
  have h1 := rk_fixV_le_autQuot_gen (A := autSub A W) (U := U.subgroupOf W)
  have h2 : rk (fixV (autSub A W)) = rk ↥(W ⊓ fixV A) := rk_fixV_autSub hAW
  have h3 : rk ↥(U.subgroupOf W ⊓ fixV (autSub A W)) = rk ↥(U ⊓ fixV A) := by
    have h4 : (U.subgroupOf W ⊓ fixV (autSub A W)).map W.subtype = U ⊓ fixV A := by
      rw [Subgroup.map_inf _ _ _ W.subtype_injective, map_subtype_fixV_autSub hAW,
        Subgroup.map_subgroupOf_eq_of_le hUW, ← inf_assoc, inf_eq_left.2 hUW]
    unfold rk
    rw [← h4, Subgroup.card_map_of_injective W.subtype_injective]
  rw [h2, h3] at h1
  exact h1

theorem rk_sec_add_gen {W U : Subgroup V} (hUW : U ≤ W) : rk (Sec W U) + rk U = rk W := by
  unfold rk
  rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', card_sec_mul hUW]

theorem rkIdx_fixV_autSec_le {A : Subgroup (MulAut V)} {M I J : Subgroup V} (hJI : J ≤ I)
    (hIM : I ≤ M) (hAM : A ≤ stabSub M) (hAI : A ≤ stabSub I) :
    rkIdx (fixV (autSec A I J)) ≤ rkIdx (fixV (autSub A M)) := by
  have e1 := rk_add_rkIdx (fixV (autSec A I J))
  have e2 := rk_sec_add_gen hJI
  have e3 := rk_inf_fixV_le_autSec_gen (A := A) hJI hAI
  have e4 : rk ↥(J ⊓ fixV A) ≤ rk ↥J := rk_mono inf_le_left
  have e5 := rkIdx_autSub_add hAM
  have e6 := rk_sup_add_rk_inf I (M ⊓ fixV A)
  have e7 : rk ↥(I ⊔ M ⊓ fixV A) ≤ rk ↥M := rk_mono (sup_le hIM inf_le_left)
  rw [← inf_assoc, inf_eq_left.2 hIM] at e6
  omega

end Sections

end CFSG.Quasithin
