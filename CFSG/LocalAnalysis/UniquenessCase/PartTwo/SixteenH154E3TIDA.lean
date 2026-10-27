module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
variable {G : Type} [Group G] [Finite G]

private theorem s16h_e3_two_mul_le_of_dvd_of_lt {d m : ℕ} (hd : 0 < d) (hdvd : d ∣ m)
    (hlt : d < m) : 2 * d ≤ m := by
  by_contra h
  have hlt' : m < 2 * d := by omega
  have hm : m ≠ 0 := by omega
  have := Nat.eq_of_dvd_of_lt_two_mul hm hdvd hlt'
  omega

theorem s16h_e3_two_mul_card_le_card_sup {Z Zx : Subgroup G} (h : Z < Z ⊔ Zx) :
    2 * Nat.card ↥Z ≤ Nat.card ↥(Z ⊔ Zx) :=
  s16h_e3_two_mul_le_of_dvd_of_lt Nat.card_pos (Subgroup.card_dvd_of_le le_sup_left)
    (Subgroup.card_lt_of_lt h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
