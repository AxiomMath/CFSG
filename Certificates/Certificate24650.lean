module

public import CFSG.Sporadic.Fi23.Centralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.SqReduce
import Certificates.Kernel.Fi23Sq.Glue

public section

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi23 CFSG.EvenSporadicStandard.TwoFi22 in
theorem certificate24650 : SqStatement D23 CFSG.Sporadic.Fi23.d :=
  by
    exact KernelFi23Sq.sqStatement24650

end Certificates

end

end
