module

public import Certificates.Kernel.Sporadic.RawTreeGen
public import Certificates.Data.Asch54SporFi22
public meta import Certificates.Data.Asch54SporFi22
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.A54F22

open CFSG.LocalAnalysis.WeakClosure81.Asch54Fi22

meta def S : Array (Array Nat) := (Array.ofFn (n := 9) fun i => tGen i.val) ++ a0Strong

meta def B : Array Nat := #[0, 1, 2, 3, 6, 4]

@[expose] def D : List (List Int) := [
  [-11, -10, -11, -10, -10, -11, -10, -10, 11, 10, 10, 11, 10, 11], [-10, 12, 10],
  [-10, -11, 13, 11, 10], [-12, -14, -13, 12, 14, 13],
  [-12, -13, -12, -14, -10, -14, -12, 10, 15, 10, 10], [-10, -11, -15, 16, 11, 10], [-17, 12, 17],
  [-12, -14, -17, 13, 17, 12], [-13, -17, 19, -10, -15, -13, 10, 18, 11]]

end CertificateChecks.KernelSpor.A54F22

#ks_rawtree CertificateChecks.KernelSpor.A54F22C 3510 12 64 64 0
  CertificateChecks.KernelSpor.A54F22.S CertificateChecks.KernelSpor.A54F22.B 11
  CertificateChecks.KernelSpor.A54F22.D

end
