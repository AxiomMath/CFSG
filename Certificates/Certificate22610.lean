module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisNXCertInputs
import Certificates.Kernel.Census.Small.C22610

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GHarris.SCert in
theorem certificate22610 :
    (∀ s : SE, s * SE.gen 6 = SE.gen 6 * s → s ∈ SE.Xlist) ∧
    (∀ s ∈ SE.Xlist, s * s = 1 → s ≠ 1 →
      s ∈ SE.LZX ∨ s = SE.gen 6 ∨ s ∈ SE.LXZ ∨ s ∈ SE.LXX) ∧
    (∀ s ∈ SE.LZX, (∃ c : SE, c⁻¹ * s * c ∈ SE.ZrepsA) ∧
      ∃ c : SE, c⁻¹ * (s * SE.gen 6) * c ∈ SE.Xreps) ∧
    (∀ s ∈ SE.LXZ, (∃ c : SE, c⁻¹ * s * c ∈ SE.Xreps) ∧
      ∃ c : SE, c⁻¹ * (s * SE.gen 6) * c ∈ SE.ZrepsA) ∧
    (∀ s ∈ SE.LXX, (∃ c : SE, c⁻¹ * s * c ∈ SE.Xreps) ∧
      ∃ c : SE, c⁻¹ * (s * SE.gen 6) * c ∈ SE.Xreps) ∧
    (∀ s ∈ SE.LZX, s ∈ SE.Xlist) ∧
    (∀ s ∈ SE.Xlist, s * SE.gen 6 = SE.gen 6 * s) ∧
    (∀ s ∈ SE.LZX, s * s = 1) ∧
    (∀ s ∈ SE.Xlist, ∀ t ∈ SE.Xlist, SE.fA (s * t) = SE.fA s + SE.fA t) ∧
    (∀ s ∈ SE.Xlist, ∀ t ∈ SE.Xlist, SE.fB (s * t) = SE.fB s + SE.fB t) ∧
    (∀ s ∈ SE.LZX, SE.fA s = 0 ∧ SE.fB s = 0) ∧
    (∀ s ∈ SE.LXZ, SE.fA s = 1 ∧ SE.fB s = 0) ∧
    (∀ s ∈ SE.LXX, SE.fB s = 1) ∧
    (∀ s ∈ SE.LZX, (∀ u ∈ SE.LZX, s * u = u * s) →
      s = SE.gen 0 ∨ s = SE.invRep 1 ∨ s = SE.invRep 1 * SE.gen 0) ∧
    (∀ s : SE, s * SE.invRep 3 = SE.invRep 3 * s → s ∈ SE.Tlist) ∧
    (∀ p ∈ SE.Xlist, ∀ q ∈ SE.Xlist, p⁻¹ * q⁻¹ * p * q * (p⁻¹ * q⁻¹ * p * q) = 1 →
      p⁻¹ * q⁻¹ * p * q = 1 ∨ p⁻¹ * q⁻¹ * p * q = SE.gen 0) ∧
    (∀ p ∈ SE.Tlist, ∀ q ∈ SE.Tlist, p⁻¹ * q⁻¹ * p * q * (p⁻¹ * q⁻¹ * p * q) = 1 →
      p⁻¹ * q⁻¹ * p * q = 1 ∨ p⁻¹ * q⁻¹ * p * q = SE.gen 0 ∨
        p⁻¹ * q⁻¹ * p * q = SE.invRep 3 ∨ p⁻¹ * q⁻¹ * p * q = SE.invRep 3 * SE.gen 0) ∧
    (∃ c : SE, c⁻¹ * (SE.invRep 3 * SE.gen 0) * c = SE.invRep 3) := KernelCensus.check22610

end Certificates
