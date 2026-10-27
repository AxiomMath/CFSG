
module


public import CFSG.Monster.B.Fischer.Fi22CertInputs
import Certificates.Kernel.Sporadic.Fi22.Cert3149

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Fischer.Native CFSG.Monster.B.Fischer in
theorem certificate3149 : CFSG.Monster.B.Fischer.Native.linesOK fi22FormsBytes 3510 = true ∧ CFSG.Monster.B.Fischer.Native.linesOK fi22InvFormBytes 1 = true ∧
      fi22StabOrbitsBytes.size = 3 * 3510 ∧ fi22MergeBytes.size = 7 * 2 * fi22MergeLength ∧
      (∀ t < 3, ∀ x ∈ fi22StabOrbit t, x < 3510) ∧
      (∀ t < 3, (fi22StabOrbit t).Pairwise (· < ·)) ∧
      ((List.range 3).map fun t => (fi22StabOrbit t).length) = [1, 2816, 693] ∧
      (fi22Merges.map fun m => (m.1 : Nat)) = [1, 11] ∧
      (fi22Merges.map fun m => m.2.length) = [3508, 3508] ∧
      (∀ m < 2, ∀ k < fi22MergeLength, (fi22MergeRaw m k).1 < 2 ∧ (fi22MergeRaw m k).2.1 < 3510 ∧
        (fi22MergeRaw m k).2.2 < 3510) := KernelSpor.F3149.c3149

end Certificates
