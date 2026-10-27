module

public import CFSG.Sporadic.SuzOddCore.Perms
import CFSG.Certificates.Kernel.CentGenRKSound
import Certificates.Kernel.CentGenK.Suz

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.CentGenK CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Sporadic.SuzOddCore
  CertificateChecks.KernelSpor in
open CFSG.Sporadic.SuzOddCore in
theorem certificate17253 : ∃ e f s₁ s₂ : Equiv.Perm (Fin 1782),
    Subgroup.closure {s₁, s₂} = suzM ∧ e ∈ suzM ∧ f ∈ suzM ∧
    e ^ 5 = 1 ∧ f ^ 5 = 1 ∧ e * f = f * e ∧ e ≠ 1 ∧ (∀ k < 5, f ≠ e ^ k) ∧
    s₁ * e = e * s₁ ∧ s₂ * f = f * s₂ := by
  have e0 : b0Arr = unpack 1782 11 Suz2306.B0 := Suz2306.b0Arr_eq
  have e1 : b1Arr = unpack 1782 11 Suz2306.B1 := Suz2306.b1Arr_eq
  have hA : PRep 1782 11 Suz2306.B0 suzB0 := prep_of_rep (by rw [← e0]; exact rep_b0)
  have hB : PRep 1782 11 Suz2306.B1 suzB1 := prep_of_rep (by rw [← e1]; exact rep_b1)
  exact cgRK_spec hA hB KernelCentGenK.Suz.suz_ok

end Certificates
