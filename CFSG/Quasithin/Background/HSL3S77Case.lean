module

public import CFSG.Quasithin.Background.HSL3S77Fix

public section

namespace CFSG.Quasithin.H.S77

open Matrix

theorem h0_case : ∀ w : Vec × Vec, (InVm w ∧ w ≠ 0) →
    ∃ c₁ c₂ ε₁ ε₂ : ZMod 2, SingDiag (c₁ • e1 + ε₁ • w.1 + ε₂ • act th0 w.1)
      (c₂ • e1 + ε₁ • w.2 + ε₂ • th0d *ᵥ w.2) := by
  decide +kernel

theorem h1_case : ∀ w : Vec × Vec, (InVm w ∧ w ≠ 0) →
    (∃ c ε₁ ε₂ : ZMod 2, SingDiag (c • e1 + ε₁ • w.1 + ε₂ • act th0 w.1)
      (ε₁ • w.2 + ε₂ • th0d *ᵥ w.2)) ∨
    ∀ g : SL32, (act g e1 = e1 ∧ act g w.1 = w.1 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ w.2 = w.2 ∧ act g (act th0 w.1) = act th0 w.1 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ (th0d *ᵥ w.2) = th0d *ᵥ w.2) → g = 1 := by
  decide +kernel

end CFSG.Quasithin.H.S77
