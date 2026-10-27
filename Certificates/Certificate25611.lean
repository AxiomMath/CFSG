module

import Certificates.Kernel.Sporadic.Fi22.CentGlue
public import CFSG.Sporadic.FischerOddCore.Fi22ExtBase

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore in
theorem certificate25611 : (∀ k < 3, ∀ z ∈ fi22P, z * z = 1 → z * fi22ExtRep k = fi22ExtRep k * z →
      (∀ y ∈ fi22P, y * fi22ExtRep k = fi22ExtRep k * y → z * y = y * z) →
      z = 1 ∨ z = fi22ExtRep k) ∧
    (∀ k, 3 ≤ k → k < 5 → ∀ z ∈ fi22R, z * z = 1 → z * fi22ExtRep k = fi22ExtRep k * z →
      (∀ y ∈ fi22R, y * fi22ExtRep k = fi22ExtRep k * y → z * y = y * z) →
      z = 1 ∨ z = fi22ExtRep k) :=
  ⟨KernelSpor.Fi22CI.centerInv_P, KernelSpor.Fi22CI.centerInv_R⟩

end Certificates
