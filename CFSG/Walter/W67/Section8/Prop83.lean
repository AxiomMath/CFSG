module

public import CFSG.Walter.W67.Section8.Arith
public import CFSG.Walter.W67.Statements

public section

namespace CFSG.Walter.W67

variable {G : Type} [Group G] [Finite G]

namespace HypI

variable (hI : HypI G)

theorem q_mod_eight : hI.q % 8 = 3 := by
  obtain ⟨k, hk⟩ := hI.odd_f
  have hq : hI.q = 3 ^ hI.f := by
    change hI.p ^ hI.f = 3 ^ hI.f
    rw [hI.p_eq_three]
  rw [hq, hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem twentyseven_le_q : 27 ≤ hI.q := by
  have hq : hI.q = 3 ^ hI.f := by
    change hI.p ^ hI.f = 3 ^ hI.f
    rw [hI.p_eq_three]
  have h3 : 3 ≤ hI.f := by
    obtain ⟨k, hk⟩ := hI.odd_f
    have := hI.one_lt_f
    omega
  rw [hq]
  calc 27 = 3 ^ 3 := by norm_num
    _ ≤ 3 ^ hI.f := Nat.pow_le_pow_right (by norm_num) h3

end HypI

theorem prop_8_3_of (h : S_ctData_of_hypII) : S_prop_8_3 := by
  intro G _ _ hII h3
  obtain ⟨d⟩ := h G hII h3
  obtain ⟨he, -⟩ := ctData_arith d hII.q_mod_eight hII.twentyseven_le_q
  exact Subgroup.eq_bot_of_card_eq _ he

end CFSG.Walter.W67
