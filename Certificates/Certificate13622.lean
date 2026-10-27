
module


public import CFSG.Sporadic.Fi23.Setup
import Certificates.Kernel.Fi23Q.RestateGlue

public section

namespace Certificates

open CertificateChecks

theorem certificate13622 : ∀ s : CFSG.Sporadic.Fi23.J, orderOf s = 3 →
    ∃ e : CFSG.Sporadic.Fi23.J, IsConj CFSG.Sporadic.Fi23.d e ∧ e * s = s * e :=
  fun s hs => KernelFi23Q.three_transposition_fixed s hs

end Certificates
