module

public import Mathlib.Tactic.Group
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteSys

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H]

theorem tx_zero (r l : H) : tx r l 0 = 1 := by
  simp [tx]

theorem tx_shift (r l : H) (a b j : ℤ) :
    r ^ (-j) * ((tx r l a)⁻¹ * tx r l b) * r ^ j = (tx r l (a + j))⁻¹ * tx r l (b + j) := by
  unfold tx
  group

theorem tx_shift_l (r l : H) (a b j : ℤ) :
    l ^ (-j) * (tx r l a * (tx r l b)⁻¹) * l ^ j = tx r l (a + j) * (tx r l (b + j))⁻¹ := by
  unfold tx
  group

end CFSG.Quasithin.Fan86.Tutte
