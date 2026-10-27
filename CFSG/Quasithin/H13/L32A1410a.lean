module

public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.Q1410

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G]

theorem eq_two_of_card_sixty {f : ℕ} (hf : 1 ≤ f) {X : Type*} [Group X] (h : IsL2Quot f X)
    (hX : Nat.card X = 60) : f = 2 := by
  have hc := h.card hf
  rw [hX] at hc
  rcases Nat.lt_or_ge f 3 with h3 | h3
  · interval_cases f
    · norm_num at hc
    · rfl
  · exfalso
    have h8 : 8 ≤ 2 ^ f := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h3
    have h64 : 64 ≤ 4 ^ f := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ 4 ^ f := Nat.pow_le_pow_right (by norm_num) h3
    have : 8 * 63 ≤ 2 ^ f * (4 ^ f - 1) := Nat.mul_le_mul h8 (by omega)
    omega

theorem card_perm_four : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem card_z2_perm_four :
    Nat.card (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) = 48 := by
  rw [Nat.card_prod, card_perm_four,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2), Nat.card_zmod]

variable [Finite G] {K I S : Subgroup G}

theorem card_oTwoQuot_of_isL2Quot_one {X : Type*} [Group X] (h : IsL2Quot 1 X) :
    Nat.card X = 6 := by
  have := h.card le_rfl
  norm_num at this
  exact this

end CFSG.Quasithin.H13.Q1410

end
