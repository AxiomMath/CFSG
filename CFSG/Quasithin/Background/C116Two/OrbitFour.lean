module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.C116Two.NatAltOdd
public import CFSG.Quasithin.Background.C116Two.NatLin2
public import CFSG.Quasithin.Background.C116Two.NatTranslate
public import CFSG.Quasithin.EmptyFaithful.S14111

public section

namespace CFSG.Quasithin.C116Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem four_mul_card_le {H L : Subgroup G} (hL : IsChiBlock H L) :
    4 * Nat.card ↥(blockZ L) ≤ Nat.card ↥(blockU L) := by
  rcases hL.2 with ⟨n, hn, hlin⟩ | ⟨m, hm, hm3, halt⟩
  · obtain ⟨F, _, _, D, hcard, -⟩ := modData_of_lin2 hlin
    rw [card_blockU_eq D, card_multiplicative_pi, hcard]
    have h4 : 4 ≤ (2 ^ n) ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ (2 ^ n) ^ 2 := Nat.le_self_pow (by norm_num) _
    calc 4 * Nat.card ↥(blockZ L) ≤ (2 ^ n) ^ 2 * Nat.card ↥(blockZ L) :=
          Nat.mul_le_mul_right _ h4
      _ = Nat.card ↥(blockZ L) * (2 ^ n) ^ 2 := by ring
  · obtain ⟨D, -⟩ := modData_of_alt hm3 halt
    rw [card_blockU_eq D,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (evenWeight m) ≃ evenWeight m),
      card_evenWeight (by omega)]
    have h4 : 4 ≤ 2 ^ (m - 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 4 * Nat.card ↥(blockZ L) ≤ 2 ^ (m - 1) * Nat.card ↥(blockZ L) := Nat.mul_le_mul_right _ h4
      _ = Nat.card ↥(blockZ L) * 2 ^ (m - 1) := by ring

end CFSG.Quasithin.C116Two
