module

public import CFSG.Quasithin.Background.B5NonA
public import CFSG.Quasithin.Background.D2Offenders

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.B5
open scoped commutatorElement

namespace B59

section Num

variable {M : Type} [CommGroup M] [Finite M]

theorem rkIdx_autSec_le (hM : ∀ v : M, v ^ 2 = 1) {A : Subgroup (MulAut M)} {U Z : Subgroup M}
    (hZU : Z ≤ U) (hAU : A ≤ stabSub U) :
    rkIdx (fixV (autSec A U Z)) ≤ rkIdx (fixV A) := by
  have h1 := rk_mu_section hM hZU hAU
  have h2 := rkIdx_autSub_add hAU
  have h3 := (rkIdx_add_le hM hAU).1
  omega

theorem rAV_autSec_le (hM : ∀ v : M, v ^ 2 = 1) {A : Subgroup (MulAut M)} {U Z : Subgroup M}
    (hZU : Z ≤ U) (hAU : A ≤ stabSub U) (hAZ : A ≤ stabSub Z) (hf : A ⊓ centSec U Z = ⊥)
    (hAne : A ≠ ⊥) (hAel : IsElemAbelian2 A) : rAV (autSec A U Z) ≤ rAV A := by
  have hrk : rk (autSec A U Z) = rk A := rk_autSec_eq hAU hAZ hf
  have hpos : 0 < rk A := hAel.rk_pos hAne
  unfold rAV
  rw [hrk]
  exact div_le_div_of_nonneg_right (by exact_mod_cast rkIdx_autSec_le hM hZU hAU)
    (by exact_mod_cast hpos.le)

end Num

section Sylow

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem index_mul_card_of_le {L A : Subgroup (MulAut V)} (hAL : A ≤ L) :
    (A.subgroupOf L).index * Nat.card ↥A = Nat.card ↥L := by
  have := (A.subgroupOf L).index_mul_card
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv] at this

theorem sylow_of_autSub {A L : Subgroup (MulAut V)} {W : Subgroup V} (hAL : A ≤ L)
    (hLW : L ≤ stabSub W) (hfL : L ⊓ centSub W = ⊥) (hfA : A ⊓ centSub W = ⊥)
    (hA2 : IsPGroup 2 A) (hS : IsSylowTwoOf (autSub A W) (autSub L W)) : IsSylowTwoOf A L := by
  have hAW : A ≤ stabSub W := hAL.trans hLW
  have hcL := card_autSub_mul hLW
  have hcA := card_autSub_mul hAW
  rw [hfL, Subgroup.card_bot, mul_one] at hcL
  rw [hfA, Subgroup.card_bot, mul_one] at hcA
  have hĀK : autSub A W ≤ autSub L W := autSub_mono hAL W
  have e1 := index_mul_card_of_le hAL
  have e2 := index_mul_card_of_le hĀK
  have hpos : 0 < Nat.card ↥A := Nat.card_pos
  have : (A.subgroupOf L).index = ((autSub A W).subgroupOf (autSub L W)).index := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [e1, ← hcA, e2, hcL]
  refine ⟨hAL, hA2, ?_⟩
  rw [this]
  exact hS.2.2

theorem sylow_of_autSec {A L : Subgroup (MulAut V)} {W U : Subgroup V} (hAL : A ≤ L)
    (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub U) (hfL : L ⊓ centSec W U = ⊥)
    (hfA : A ⊓ centSec W U = ⊥) (hA2 : IsPGroup 2 A) {B : Subgroup (MulAut (Sec W U))}
    (hBA : B ≤ autSec A W U) (hS : IsSylowTwoOf B (autSec L W U)) : IsSylowTwoOf A L := by
  have hAW : A ≤ stabSub W := hAL.trans hLW
  have hAU : A ≤ stabSub U := hAL.trans hLU
  have hcL := card_autSec_mul hLW hLU
  have hcA := card_autSec_mul hAW hAU
  rw [hfL, Subgroup.card_bot, mul_one] at hcL
  rw [hfA, Subgroup.card_bot, mul_one] at hcA
  have hPQ : autSec A W U ≤ autSec L W U := autSec_mono hAL W U
  have e1 := index_mul_card_of_le hAL
  have e2 := index_mul_card_of_le hPQ
  have hpos : 0 < Nat.card ↥A := Nat.card_pos
  have hidx : (A.subgroupOf L).index = ((autSec A W U).subgroupOf (autSec L W U)).index := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [e1, ← hcA, e2, hcL]
  refine ⟨hAL, hA2, ?_⟩
  rw [hidx]
  intro hdvd
  apply hS.2.2
  exact hdvd.trans (Subgroup.index_dvd_of_le (fun x hx => hBA hx))

end Sylow

end B59

end FFC

end CFSG.Quasithin
