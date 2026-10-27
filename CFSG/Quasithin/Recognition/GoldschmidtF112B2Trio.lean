module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.Quasithin.F112B2

open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem perm_fin3_mul_involutions : ∀ σ τ : Equiv.Perm (Fin 3), σ ≠ 1 → σ * σ = 1 → τ ≠ 1 →
    τ * τ = 1 → σ ≠ τ → (σ * τ) ^ 3 = 1 ∧ σ * τ ≠ 1 := by
  decide

end CFSG.Quasithin.F112B2
