module

public import CFSG.Quasithin.Background.HSL3Six

public section

namespace CFSG.Quasithin.H.SL3Six

open Matrix

@[expose] def mulVec3 (a : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    Fin 3 → ZMod 2 :=
  fun i => a i 0 * v 0 + a i 1 * v 1 + a i 2 * v 2

theorem mulVec3_eq (a : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    mulVec3 a v = a *ᵥ v := by
  funext i
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rfl

theorem card_fix_three3 : ∀ g : Matrix (Fin 3) (Fin 3) (ZMod 2), mul3 g (mul3 g g) = 1 → g ≠ 1 →
    (Finset.univ.filter fun v : Fin 3 → ZMod 2 => mulVec3 g v = v).card = 2 := by
  decide +kernel

theorem card_fix_three (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h3 : g * g * g = 1) (h1 : g ≠ 1) :
    (Finset.univ.filter fun v : Fin 3 → ZMod 2 => g *ᵥ v = v).card = 2 := by
  have h := card_fix_three3 g (by rw [mul3_eq, mul3_eq, ← mul_assoc]; exact h3) h1
  simpa only [mulVec3_eq] using h

end CFSG.Quasithin.H.SL3Six
