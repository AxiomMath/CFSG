module

public import CFSG.Monster.AxisCount.HSIdentBase
public import CFSG.Monster.AxisCount.HSIdentRec5Inputs
import Certificates.Kernel.KDenseP.Axis.C6015

public section

namespace Certificates

open CFSG CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.AxisCount.HS in
theorem certificate6015 : ∀ s ∈ recShard_5, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, RecSpec s.1 r ε :=
  CertificateChecks.KernelKDenseP.Axis.c6015

end Certificates
