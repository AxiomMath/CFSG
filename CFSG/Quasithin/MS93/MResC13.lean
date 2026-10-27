module

public import CFSG.Quasithin.MS93.MResDefs
public import CFSG.Quasithin.MS93.ASC134Ord

public section

namespace CFSG.Quasithin.MS93.MRes

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped Pointwise

section Order

variable {G : Type} [Group G]

theorem le_sl3Order {n : ℕ} (hn : 2 ≤ n) :
    60480 ≤ (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := by
  have hq : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h3 : 64 ≤ (2 ^ n) ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 16 ≤ (2 ^ n) ^ 2 := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
  calc 60480 = 64 * 15 * 63 := by norm_num
    _ ≤ (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h3 (by omega)) (by omega)

theorem notSL3Big_of_isModO2Surj_two {L : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) {α : ↥L →* ↥(StatedSL 3 F)} (hα : IsModO2Surj L α) :
    NotSL3Big L := by
  rintro ⟨n, F', _, _, α', hn, hF', hα'⟩
  have h1 := card_quot_of_isModO2Surj hα
  have h2 := card_quot_of_isModO2Surj hα'
  rw [card_statedSL3_eq (n := 1) (by rw [hF, pow_one])] at h1
  rw [card_statedSL3_eq hF'] at h2
  have h3 := le_sl3Order hn
  norm_num at h1
  omega

end Order

end CFSG.Quasithin.MS93.MRes
