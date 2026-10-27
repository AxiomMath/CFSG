module

public import Certificates.Data.NT44Commutator
import Certificates.Kernel.NT44.CommGlue

public section

namespace Certificates

open CertificateChecks

theorem certificate1212004 : CFSG.GH74.GLS.NT44.PermutationNative.commutatorCheck () = true := by
  rw [CFSG.GH74.GLS.NT44.PermutationNative.commutatorCheck.eq_1]
  exact decide_eq_true KernelNT44.CommGlue.nt44_comm

end Certificates
