module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B4L3Fin
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

namespace N1246

namespace SL27

open CFSG.Quasithin CFSG.Quasithin.L3

theorem gamma_AS_noncomm : ∀ c : L3.Vec, c ≠ 0 → ∀ δ : L3.Γ, L3.act δ c = c → δ * δ * δ = 1 →
    δ ≠ 1 → ∀ τ ∈ L3.AS {0, c}, τ ≠ 1 → τ * δ ≠ δ * τ := by
  decide +kernel

theorem gamma_two_mem_AS : ∀ c : L3.Vec, c ≠ 0 → ∀ τ : L3.Γ, τ ^ 8 = 1 → L3.act τ c = c →
    τ * τ * τ ∈ L3.AS {0, c} → τ ∈ L3.AS {0, c} := by
  decide +kernel

set_option synthInstance.maxSize 8192 in
theorem gamma_AS_three : ∀ c : L3.Vec, c ≠ 0 → ∀ τ₁ ∈ L3.AS {0, c}, ∀ τ₂ ∈ L3.AS {0, c},
    ∀ τ ∈ L3.AS {0, c}, τ₁ ≠ 1 → τ₂ ≠ 1 → τ₁ ≠ τ₂ → τ ≠ 1 →
    τ = τ₁ ∨ τ = τ₂ ∨ τ = τ₁ * τ₂ := by
  decide +kernel

end SL27

end N1246

end CFSG.Quasithin.H13
