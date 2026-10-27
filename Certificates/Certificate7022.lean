module

public import CFSG.Quasithin.Background.HA7DataInputs
import CFSG.Certificates.Kernel.Misc.A7GL42

public section

namespace Certificates

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.A7 Equiv in
open scoped Matrix in
theorem certificate7022 :
    (∀ σ : alternatingGroup (Fin 7), σ * σ = 1 → σ ≠ 1 →
       ∃ g : alternatingGroup (Fin 7), g * σ * g⁻¹ = inv7)
    ∧ ((Finset.univ.filter fun π : alternatingGroup (Fin 8) => π * inv8 = inv8 * π).card = 96)
    ∧ ((Finset.univ.filter fun M : Matrix (Fin 4) (Fin 4) (ZMod 2) => M * M = 1 ∧
       (Finset.univ.filter fun v : Fin 4 → ZMod 2 => M *ᵥ v = v).card = 8).card = 105)
    ∧ (∀ M : Matrix (Fin 4) (Fin 4) (ZMod 2), M ^ 5 = 1 → M ≠ 1 →
       ∀ v : Fin 4 → ZMod 2, M *ᵥ v = v → v = 0) :=
  ⟨CFSG.KC.Misc.A7GL42.exists_conj_inv7, CFSG.KC.Misc.A7GL42.card_centralizer_inv8,
    CFSG.KC.Misc.A7GL42.card_transvections, CFSG.KC.Misc.A7GL42.fix_eq_zero_of_pow_five⟩

end Certificates
