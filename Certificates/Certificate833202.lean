module

public import Certificates.Kernel.Co2HeavyK.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Blueprint in
theorem certificate833202 : ∃ V₀ H : Subgroup NativeSporadic.Co2,
    (∀ E : Subgroup NativeSporadic.Co2, CFSG.Open.IsElemAbelian 2 E → 2 ^ 10 ≤ Nat.card E →
      ∃ g : NativeSporadic.Co2, E.map (MulAut.conj g).toMonoidHom = V₀) ∧
    H ≤ Subgroup.normalizer (V₀ : Set NativeSporadic.Co2) ∧ IsSimpleGroup H ∧
      ¬ IsMulCommutative H ∧ Nat.card H = 443520 :=
  KernelCo2HeavyK.co2_v0_m22K

end Certificates
