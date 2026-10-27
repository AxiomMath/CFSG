module

public import CFSG.Quasithin.H13.GoldschmidtM22EndS3

public section

namespace CFSG.Quasithin.H13.GM22

open Equiv

theorem perm3_prod_noncomm :
    ∀ τ σ : Perm (Fin 3), τ.support.card = 2 → σ * τ ≠ τ * σ →
      (τ * (σ⁻¹ * τ * σ)) * τ ≠ τ * (τ * (σ⁻¹ * τ * σ)) := by
  decide +kernel

theorem perm3_prod_pow_four :
    ∀ τ σ : Perm (Fin 3), τ.support.card = 2 → σ * τ ≠ τ * σ →
      (τ * (σ⁻¹ * τ * σ)) ^ 4 = τ * (σ⁻¹ * τ * σ) := by
  decide +kernel

end CFSG.Quasithin.H13.GM22
