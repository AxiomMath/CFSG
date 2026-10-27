module

public import CFSG.Sporadic.FischerOddCore.Fi22SylowWit
import Certificates.Kernel.Sporadic.Fi22.S2072Final

public section

open CFSG.Sporadic.FischerOddCore

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.FischerOddCore in
theorem certificate2072 : ∀ s < 11,
    fi22CentSylowSub s ≤ fi22H (fi22CentSylowField s 0) ∧
    Nat.card (fi22CentSylowSub s) = fi22CentSylowField s 2 ∧
    (∀ g ∈ fi22CentSylowSub s, g ≠ 1 → g ^ fi22CentSylowField s 1 = 1 →
      ∃ w < fi22CentSylowField s 7, ∃ t ∈ fi22CentSylowSub s, ∃ j, 0 < j ∧
        j < fi22CentSylowField s 1 ∧ g = t * fi22SylX s w ^ j * t⁻¹) ∧
    (∀ w < fi22CentSylowField s 7,
      fi22SylX s w ≠ 1 ∧ fi22SylX s w ^ fi22CentSylowField s 1 = 1 ∧
      fi22SylX s w ∈ fi22H (fi22CentSylowField s 0) ∧
      fi22SylH s w ∈ fi22H (fi22CentSylowField s 0) ∧
      ∃ k, (fi22SylX s w * fi22SylH s w * fi22SylX s w * (fi22SylH s w)⁻¹) ^ k ≠ 1 ∧
        ((fi22SylX s w * fi22SylH s w * fi22SylX s w * (fi22SylH s w)⁻¹) ^ k) ^ 2 = 1) := KernelSpor.S2072.facts2072

end Certificates

end
