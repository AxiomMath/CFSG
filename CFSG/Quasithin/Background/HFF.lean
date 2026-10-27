module

public import CFSG.Quasithin.Background.HDefs

public section

namespace CFSG.Quasithin

namespace H

open CFSG.Open

variable {V : Type*} [CommGroup V] [Finite V]

theorem index_eq_two_pow_rkIdx (hV : IsPGroup 2 V) (U : Subgroup V) :
    U.index = 2 ^ rkIdx U := by
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).mp hV
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hm ▸ U.index_dvd_card)
  unfold rkIdx
  rw [hk, padicValNat.prime_pow]

theorem isFOneOffender_of_card_le (hV : IsPGroup 2 V) {X A : Subgroup (MulAut V)} (hAX : A ≤ X)
    (hA1 : A ≠ ⊥) (hAel : IsElemAbelian2 A)
    (h : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) : IsFOneOffender X A := by
  refine ⟨⟨hAX, hA1, hAel⟩, ?_⟩
  have hpA : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hAel.2 x x.2)⟩
  have hA : Nat.card A = 2 ^ rk ↥A := card_eq_two_pow_of_isPGroup hpA
  have h1 := (fixV A).card_mul_index
  rw [index_eq_two_pow_rkIdx hV] at h1
  rw [hA] at h
  have hpos : 0 < Nat.card (fixV A) := Nat.card_pos
  have h2 : 2 ^ rkIdx (fixV A) ≤ 2 ^ rk ↥A := by
    have : Nat.card (fixV A) * 2 ^ rkIdx (fixV A) ≤ Nat.card (fixV A) * 2 ^ rk ↥A := by
      rw [h1, mul_comm (Nat.card (fixV A))]
      exact h
    exact Nat.le_of_mul_le_mul_left this hpos
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  omega

theorem isFOneModule_of_isFFModule (hV : IsPGroup 2 V) {X : Subgroup (MulAut V)}
    (h : IsFFModule X) : IsFOneModule X := by
  obtain ⟨A, hAX, hA1, hAel, hcard⟩ := h
  exact ⟨A, isFOneOffender_of_card_le hV hAX hA1 hAel hcard⟩

theorem not_isFFModule_of_not_isFOneModule (hV : IsPGroup 2 V) {X : Subgroup (MulAut V)}
    (h : ¬ IsFOneModule X) : ¬ IsFFModule X := fun hFF => h (isFOneModule_of_isFFModule hV hFF)

end H

end CFSG.Quasithin
