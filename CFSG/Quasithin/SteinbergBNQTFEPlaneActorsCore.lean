module

public import CFSG.Quasithin.SteinbergBNQTFEElementaryTwentySeven

public section

namespace CFSG.Quasithin.SteinbergBN

open Subgroup Module CFSG.QuasithinUnique.Setup.Offender

namespace PlaneActors

variable {F : Type*} [Field F] {D : Type*} [AddCommGroup D] [Module F D]

theorem pRank_two_le_one {P : Type*} [Group P] [Finite P] (z : P)
    (hz : ∀ x : P, orderOf x = 2 → x = z) : CFSG.pRank 2 P ≤ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine csSup_le ⟨0, ⊥, TwentySeven.isElementaryAbelian_of_forall
    (fun a ha b hb => by rw [mem_bot.1 ha, mem_bot.1 hb]) (fun a ha => by rw [mem_bot.1 ha,
      one_pow]), by simp⟩ ?_
  rintro r ⟨A, hA, hcard⟩
  have hsq : ∀ c : A, c ^ 2 = 1 := fun c =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p 2 A) c
  have hle : Nat.card A ≤ 2 := by
    have hinj : Function.Injective (fun a : A => decide (a = 1)) := by
      intro a b hab
      by_cases ha : a = 1 <;> by_cases hb : b = 1
      · rw [ha, hb]
      · simp [ha, hb] at hab
      · simp [ha, hb] at hab
      · have hoa : orderOf (a : P) = 2 := by
          rw [Subgroup.orderOf_coe]
          exact orderOf_eq_prime (hsq a) ha
        have hob : orderOf (b : P) = 2 := by
          rw [Subgroup.orderOf_coe]
          exact orderOf_eq_prime (hsq b) hb
        exact Subtype.ext ((hz _ hoa).trans (hz _ hob).symm)
    have h := Nat.card_le_card_of_injective _ hinj
    simpa using h
  rw [hcard] at hle
  by_contra h
  have : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

variable [Finite F] (h2 : (2 : F) ≠ 0) (hD : finrank F D = 2)
  {J : Subgroup (LinearMap.GeneralLinearGroup F D)}

end PlaneActors

end CFSG.Quasithin.SteinbergBN
