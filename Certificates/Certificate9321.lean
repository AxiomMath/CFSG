module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25MixInputs

public section

open CFSG.ClassicalInvolution.Hat2A7 Equiv Equiv.Perm

namespace CertificateChecks.Batch9321

open CFSG.ClassicalInvolution.Hat2A7 Equiv Equiv.Perm

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem four_le_filter_D8list : ∀ σ : Perm (Fin 7), σ * σ = 1 →
    σ * (sD : Perm (Fin 7)) * σ⁻¹ ∈ D8list.map (fun d : A7 => (d : Perm (Fin 7))) →
    σ * (tD : Perm (Fin 7)) * σ⁻¹ ∈ D8list.map (fun d : A7 => (d : Perm (Fin 7))) →
      4 ≤ (D8list.filter (fun d : A7 => decide ((d : Perm (Fin 7)) * σ = σ * d))).length := by
  decide +kernel

end CertificateChecks.Batch9321

namespace Certificates

open CertificateChecks

open CFSG.ClassicalInvolution.Hat2A7 Equiv Equiv.Perm in
theorem certificate9321 : ∀ σ : Perm (Fin 7), σ * σ = 1 →
    σ * (sD : Perm (Fin 7)) * σ⁻¹ ∈ D8list.map (fun d : A7 => (d : Perm (Fin 7))) →
    σ * (tD : Perm (Fin 7)) * σ⁻¹ ∈ D8list.map (fun d : A7 => (d : Perm (Fin 7))) →
      4 ≤ (D8list.filter (fun d : A7 => decide ((d : Perm (Fin 7)) * σ = σ * d))).length :=
  CertificateChecks.Batch9321.four_le_filter_D8list

end Certificates
