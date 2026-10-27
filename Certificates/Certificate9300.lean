module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7FactsInputs
import Certificates.Kernel.Hat2A7.Facts

public section

namespace Certificates

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7 in
open Equiv Equiv.Perm in
theorem certificate9300 : (∀ y : A7, y ≠ 1 → y * y = 1 → ∃ g : A7, g * tD * g⁻¹ = y)
    ∧ (∀ σ : Perm (Fin 7), σ * (sD : Perm (Fin 7)) = (sD : Perm (Fin 7)) * σ →
      σ * (tD : Perm (Fin 7)) = (tD : Perm (Fin 7)) * σ → σ * σ = 1)
    ∧ (∀ σ : Perm (Fin 7), σ * σ = 1 → σ ≠ 1 →
      ∃ a : A7, (a : Perm (Fin 7))⁻¹ * σ * a ≠ σ ∧
        ((a : Perm (Fin 7))⁻¹ * σ * a) * σ = σ * ((a : Perm (Fin 7))⁻¹ * σ * a))
    ∧ (∀ σ : Perm (Fin 7), σ * σ = 1 →
      Fintype.card {a : A7 // (a : Perm (Fin 7)) * σ = σ * a} % 16 = 8) :=
  ⟨Kernel.Hat2A7.a7_involution_conj, Kernel.Hat2A7.sq_eq_one_of_commute_gens,
    Kernel.Hat2A7.exists_commuting_conj, Kernel.Hat2A7.card_evenCentralizer_mod⟩

end Certificates
