
module


public import Certificates.Kernel.Sporadic.Fi24G2g.C2078

public section

namespace Certificates

open CertificateChecks

theorem certificate2078 : CFSG.Sporadic.FischerOddCore.Wit2078Facts :=
  by intros; exact KernelFi24G2g.wit2078_facts KernelFi24OrbL.pt_sp_rank

end Certificates
