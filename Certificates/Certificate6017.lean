module

public import CFSG.Monster.AxisCount.HSIdentBase
public import CFSG.Monster.AxisCount.HSIdentRec7Inputs
import Certificates.Kernel.KDenseP.Axis.C6017

public section

namespace Certificates

open CFSG CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.AxisCount.HS in
theorem certificate6017 : ∀ s ∈ recShard_7, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, RecSpec s.1 r ε :=
  CertificateChecks.KernelKDenseP.Axis.c6017

end Certificates
