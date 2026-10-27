module

public import Certificates.Kernel.Sporadic.Fi24G2g.C2333

public section

namespace Certificates

open CertificateChecks

theorem certificate2333 : CFSG.Sporadic.FischerOddCore.Outer2333Facts :=
  by intros; exact KernelFi24G2g.outer2333_facts KernelFi24OrbL.pt_sp_rank

end Certificates
