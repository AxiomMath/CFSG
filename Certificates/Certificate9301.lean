module

import Certificates.Kernel.Direct.C9301
public import CFSG.Adapters.ProjectiveSpecialLinear
public import Certificates.Certificate43

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelDirect.C9301 in
open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Nobq in
open Equiv Equiv.Perm in
theorem certificate9301 : (∀ (d : Perm (Fin 4)), (∀ i, (d * d) i ≠ i) → ∀ (ε : ℤˣ),
      ∃ u : Perm (Fin 4), sign u = ε ∧ u * (d * d) = (d * d) * u ∧
        (d * (u * d * u⁻¹)) * (d * (u * d * u⁻¹)) = 1)
    ∧ (∀ (r : Perm (Fin 4)), r * r = 1 → r ≠ 1 →
      ∃ v : Perm (Fin 4), (r * (v * r * v⁻¹)) * (r * (v * r * v⁻¹)) = 1 ∧ r * (v * r * v⁻¹) ≠ 1)
    ∧ (∀ (r : Perm (Fin 5)), r * r = 1 → r ≠ 1 →
      ∃ v : Perm (Fin 5), (r * (v * r * v⁻¹)) * (r * (v * r * v⁻¹)) = 1 ∧ r * (v * r * v⁻¹) ≠ 1)
    ∧ (∀ (r : Perm (Fin 6)), r * r = 1 → r ≠ 1 →
      ∃ v : Perm (Fin 6), (r * (v * r * v⁻¹)) * (r * (v * r * v⁻¹)) = 1 ∧ r * (v * r * v⁻¹) ≠ 1)
    ∧ (∀ (r : Perm (Fin 7)), r * r = 1 → r ≠ 1 →
      ∃ v : Perm (Fin 7), (r * (v * r * v⁻¹)) * (r * (v * r * v⁻¹)) = 1 ∧ r * (v * r * v⁻¹) ≠ 1) :=
  ⟨exists_commuting_odd_check, exists_conj_involution_four, exists_conj_involution_five,
    exists_conj_involution_six, exists_conj_involution_seven⟩

end Certificates
