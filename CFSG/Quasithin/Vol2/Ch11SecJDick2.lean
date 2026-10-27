module

public import CFSG.Quasithin.Vol2.Ch11SecJDick1

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecJ

open Matrix
open scoped Matrix

variable {F : Type*} [Field F]

theorem upper_pow {g : GL (Fin 2) F} (h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (k : ℕ) :
    ((g ^ k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ((g ^ k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
        (g : Matrix (Fin 2) (Fin 2) F) 0 0 ^ k ∧
      ((g ^ k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
        (g : Matrix (Fin 2) (Fin 2) F) 1 1 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    rw [pow_succ, Units.val_mul]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, i1, i2, i3, h10, pow_succ]
    exact ⟨by ring, by ring, by ring⟩

theorem exists_pow_prime_power [Finite F] {g : GL (Fin 2) F}
    (h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (hd : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ (g : Matrix (Fin 2) (Fin 2) F) 1 1) :
    ∃ r e m : ℕ, r.Prime ∧ r ∣ Nat.card F - 1 ∧ orderOf (g ^ m) = r ^ e ∧
      ((g ^ m : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ((g ^ m : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 ≠
        ((g ^ m : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set a := (g : Matrix (Fin 2) (Fin 2) F) 0 0 with ha_def
  set b := (g : Matrix (Fin 2) (Fin 2) F) 1 1 with hb_def
  have hdet : a * b ≠ 0 := by
    have h1 := ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
    rwa [Matrix.det_fin_two, h10, mul_zero, sub_zero] at h1
  have ha : a ≠ 0 := left_ne_zero_of_mul hdet
  have hb : b ≠ 0 := right_ne_zero_of_mul hdet
  set u : Fˣ := Units.mk0 (a / b) (div_ne_zero ha hb) with hu
  have hu1 : u ≠ 1 := by
    intro h
    apply hd
    have h2 := congrArg Units.val h
    rw [hu, Units.val_mk0, Units.val_one] at h2
    exact (div_eq_one_iff_eq hb).1 h2
  have hd1 : orderOf u ≠ 1 := fun h => hu1 (orderOf_eq_one_iff.1 h)
  have hr : (orderOf u).minFac.Prime := Nat.minFac_prime hd1
  have hrd : (orderOf u).minFac ∣ orderOf u := Nat.minFac_dvd _
  have hdq : orderOf u ∣ Nat.card F - 1 := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_units]
    exact orderOf_dvd_card
  obtain ⟨e, m, hrm, hN⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' (orderOf u).minFac hr.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hN
    exact (orderOf_pos g).ne' hN
  refine ⟨(orderOf u).minFac, e, m, hr, hrd.trans hdq, ?_, (upper_pow h10 m).1, ?_⟩
  · rw [orderOf_pow_of_dvd hm0 ⟨(orderOf u).minFac ^ e, by rw [hN, mul_comm]⟩, hN,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  · rw [(upper_pow h10 m).2.1, (upper_pow h10 m).2.2]
    intro h
    apply hrm
    refine hrd.trans (orderOf_dvd_of_pow_eq_one ?_)
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hu, Units.val_mk0, Units.val_one, div_pow, h,
      div_self (pow_ne_zero m hb)]

end CFSG.Quasithin.Vol2.Ch11.SecJ
