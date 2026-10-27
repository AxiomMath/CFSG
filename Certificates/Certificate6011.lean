module

public import CFSG.Monster.AxisCount.HSIdentBase
public import CFSG.Monster.AxisCount.HSIdentRec1Inputs
import Certificates.Kernel.KDenseP.Axis.C6011

public section

namespace Certificates

open CFSG CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.AxisCount.HS in
theorem certificate6011 : ∀ s ∈ recShard_1, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, RecSpec s.1 r ε :=
  CertificateChecks.KernelKDenseP.Axis.c6011

end Certificates
