module

public import CFSG.Quasithin.H13.A6S13829a

public section

namespace CFSG.Quasithin.H13.A6

open Matrix

theorem wedge2_mul (A B : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    wedge2 (A * B) = wedge2 A * wedge2 B := by
  ext p q
  have key : ∀ M : Matrix (Fin 6) (Fin 6) (ZMod 2), M p q = (M.mulVec (Pi.single q 1)) p := by
    intro M
    rw [mulVec_single_one]
    rfl
  rw [key (wedge2 (A * B)), key (wedge2 A * wedge2 B), ← mulVec_mulVec, ← pl_single q,
    wedge2_mulVec_pl, wedge2_mulVec_pl, wedge2_mulVec_pl, mulVec_mulVec, mulVec_mulVec]

theorem wedge2_mulVec_mulVec (A B : Matrix (Fin 4) (Fin 4) (ZMod 2)) (x : Fin 6 → ZMod 2) :
    (wedge2 A).mulVec ((wedge2 B).mulVec x) = (wedge2 (A * B)).mulVec x := by
  rw [wedge2_mul, mulVec_mulVec]

theorem wedge2_one : wedge2 (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
  decide

end CFSG.Quasithin.H13.A6
