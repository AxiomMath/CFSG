module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1U0
import Certificates.Kernel.PermCent.U43QuatFinal
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Q8
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Chain

public section

namespace Certificates

open CertificateChecks

open CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M CFSG.ClassicalInvolution.Generic in
open CFSG.EvenSporadicStandard.M24Std.CU43 (P) in
theorem certificate55121 : (r0P ∈ P ∧ u0P ∈ P ∧ v0P ∈ P ∧ u1P ∈ P ∧ v1P ∈ P ∧ s01P ∈ P ∧ w0P ∈ P ∧ y0P ∈ P ∧
      ∀ c ∈ gamP, c ∈ P) ∧
    (r0P ≠ 1 ∧ r0P * r0P = 1 ∧ u0P * u0P = r0P ∧ (∀ x, x ∈ K0 ↔ x ∈ L0P) ∧
      u1P * u1P = r0P ∧ (∀ x, x ∈ K1 ↔ x ∈ L1P) ∧ d2P * u0P = u0P * d2P ∧
      d2P * v0P = v0P * d2P ∧ d2P * v1P ≠ v1P * d2P ∧ s01P * s01P = 1 ∧
      s01P * r0P = r0P * s01P ∧ conjSub s01P K1 = K0 ∧ conjSub s01P K0 = K1 ∧
      w0P * r0P = r0P * w0P ∧ (∀ c ∈ gamP, conjSub c K0 = K0) ∧
      y0P * (y0P * y0P) = 1 ∧ y0P * d2P = d2P * y0P ∧ conjSub y0P K0 = K0 ∧
      y0P * u0P ≠ u0P * y0P) ∧
    ∀ K : Subgroup (Equiv.Perm (Fin 820)),
      CFSG.ClassicalInvolution.Q3.TL4.Vtx.AmbientQuatDatum P K r0P → K = K0 ∨ K = K1 := KernelPermCent.U43Quat.facts55121

end Certificates
