module

public import CFSG.Monster.AxisCount.HSIdentBase
public import CFSG.Monster.AxisCount.HSIdentRec0Inputs
import Certificates.Kernel.KDenseP.Axis.C6010

public section

namespace Certificates

open CFSG CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.AxisCount.HS in
theorem certificate6010 : ∀ s ∈ recShard_0, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, RecSpec s.1 r ε :=
  CertificateChecks.KernelKDenseP.Axis.c6010

end Certificates
