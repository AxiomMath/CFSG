module

public import CFSG.Quasithin.EmptyFaithful.S143NAInputs
import CFSG.Adapters.ProjectiveSpecialLinear

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.S143 CFSG.Quasithin.S143.A6Model

namespace CertificateChecks.Batch7950

open CFSG CFSG.Quasithin CFSG.Quasithin.S143 CFSG.Quasithin.S143.A6Model

set_option maxRecDepth 100000 in
private theorem conf6plus_one_swap_0 :
    ∀ p : Fin 6, Equiv.swap 3 4 p ≠ p → Equiv.swap 3 4 = Equiv.swap p (Equiv.swap 3 4 p) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem conf6plus_one_rEven_1 :
    ∀ w : Fin 6 → ZMod 2, VanL Vr1 w → wEven w := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem conf6plus_one_vr_sign_2 :
    ∀ σ ∈ Vr1, σ.sign = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem conf6plus_one_rMoves_3 :
    ∀ p : Fin 6, Equiv.swap 3 4 p ≠ p → ∃ σ ∈ Vr1, σ p ≠ p := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem conf6plus_two_swap_4 :
    ∀ p : Fin 6, Equiv.swap 0 4 p ≠ p → Equiv.swap 0 4 = Equiv.swap p (Equiv.swap 0 4 p) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem conf6plus_two_rEven_5 :
    ∀ w : Fin 6 → ZMod 2, VanL Vr2 w → wEven w := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem conf6plus_two_vr_sign_6 :
    ∀ σ ∈ Vr2, σ.sign = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem conf6plus_two_rMoves_7 :
    ∀ p : Fin 6, Equiv.swap 0 4 p ≠ p → ∃ σ ∈ Vr2, σ p ≠ p := by
  decide +kernel

end CertificateChecks.Batch7950

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.S143 CFSG.Quasithin.S143.A6Model in
theorem certificate7950 :
    (∀ p : Fin 6, Equiv.swap 3 4 p ≠ p → Equiv.swap 3 4 = Equiv.swap p (Equiv.swap 3 4 p))
    ∧ (∀ w : Fin 6 → ZMod 2, VanL Vr1 w → wEven w)
    ∧ (∀ σ ∈ Vr1, σ.sign = 1)
    ∧ (∀ p : Fin 6, Equiv.swap 3 4 p ≠ p → ∃ σ ∈ Vr1, σ p ≠ p)
    ∧ (∀ p : Fin 6, Equiv.swap 0 4 p ≠ p → Equiv.swap 0 4 = Equiv.swap p (Equiv.swap 0 4 p))
    ∧ (∀ w : Fin 6 → ZMod 2, VanL Vr2 w → wEven w)
    ∧ (∀ σ ∈ Vr2, σ.sign = 1)
    ∧ (∀ p : Fin 6, Equiv.swap 0 4 p ≠ p → ∃ σ ∈ Vr2, σ p ≠ p) := by
  exact ⟨CertificateChecks.Batch7950.conf6plus_one_swap_0, CertificateChecks.Batch7950.conf6plus_one_rEven_1,
    CertificateChecks.Batch7950.conf6plus_one_vr_sign_2, CertificateChecks.Batch7950.conf6plus_one_rMoves_3,
    CertificateChecks.Batch7950.conf6plus_two_swap_4, CertificateChecks.Batch7950.conf6plus_two_rEven_5,
    CertificateChecks.Batch7950.conf6plus_two_vr_sign_6, CertificateChecks.Batch7950.conf6plus_two_rMoves_7⟩

end Certificates
