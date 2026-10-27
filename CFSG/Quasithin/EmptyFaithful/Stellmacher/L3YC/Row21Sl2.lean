module

public import CFSG.Assembly.OrderReductions.LinearOrders

public section

namespace CFSG.Quasithin

open scoped Matrix

namespace Stellmacher.L3YC

namespace Row21

theorem card_sl2 (p : ℕ) [Fact p.Prime] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) := by
  have := CFSG.OrderReductions.LinearOrders.card_specialLinear (ZMod p) 2 (by norm_num)
  rw [this]
  simp [Finset.Icc_self]

theorem card_sl2_seven : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) = 336 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [card_sl2]
  norm_num

theorem sq_eq_one : ∀ M : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7), M * M = 1 → M = 1 ∨ M = -1 := by
  decide +kernel

theorem three_no_fixed : ∀ M : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7), M ^ 3 = 1 → M ≠ 1 →
    ∀ w : Fin 2 → ZMod 7, (M : Matrix (Fin 2) (Fin 2) (ZMod 7)) *ᵥ w = w → w = 0 := by
  decide +kernel

theorem neg_one_mul : ∀ M : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7), (-1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) * M = M * (-1) := by
  decide +kernel

theorem neg_mulVec (w : Fin 2 → ZMod 7) :
    (((-1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) :
      Matrix (Fin 2) (Fin 2) (ZMod 7)) *ᵥ w = -w := by
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_mulVec,
    Matrix.one_mulVec]

theorem neg_one_mul_neg_one :
    (-1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) * (-1) = 1 := by
  decide +kernel

theorem neg_one_ne_one : (-1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) ≠ 1 := by
  decide +kernel

theorem not_commutative :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7), a * b ≠ b * a := by
  decide +kernel

end Row21

end Stellmacher.L3YC

end CFSG.Quasithin
