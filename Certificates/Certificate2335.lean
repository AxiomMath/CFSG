module

import Certificates.Kernel.Th.Fam.C2335
import Certificates.Kernel.Th.Fam.Ctx
public import CFSG.Sporadic.Th.Max3.DataBase

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Th Subgroup CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 in
theorem certificate2335 : eqRows (mulRows rowsA rowsB) (mulRows rowsB rowsA) = false := by
  kernel_exact CFSG.KC.Th.Expr.facts_of KernelTh.Fam.thCtx KernelTh.Fam.l2335 KernelTh.Fam.ok2335

end Certificates
