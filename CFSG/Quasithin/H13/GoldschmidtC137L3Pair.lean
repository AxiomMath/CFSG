module

public import CFSG.Quasithin.Background.B4L3Fin

public section

namespace CFSG.Quasithin.H13.U3.GC137

open CFSG.Quasithin.L3

set_option maxRecDepth 100000 in
theorem stab_pair_cases : ∀ e₁ e₂ : Vec, (e₁ ≠ 0 ∨ e₂ ≠ 0) →
    (∃ e₀ : Vec, e₀ ≠ 0 ∧ (e₁ = 0 ∨ e₁ = e₀) ∧ (e₂ = 0 ∨ e₂ = e₀)) ∨
      (∀ g : Γ, act g e₁ = e₁ → act g e₂ = e₂ → g * g = 1) := by decide +kernel

end CFSG.Quasithin.H13.U3.GC137
