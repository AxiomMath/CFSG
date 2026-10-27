module

public import Certificates.Data.Kernel.Cert690.CensusSBind
public import Certificates.Kernel.Cert690.CensSPB
public import Certificates.Kernel.Cert690.CensSMB

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.CensSBind

open CFSG.KC.C690S

theorem bindP : bindS false CertificateChecks.KernelC690.CensSP.base = true := by decide +kernel

theorem bindM : bindS true CertificateChecks.KernelC690.CensSM.base = true := by decide +kernel

theorem badSignP : bindS true CertificateChecks.KernelC690.CensSP.base = false := by
  decide +kernel

theorem badSignM : bindS false CertificateChecks.KernelC690.CensSM.base = false := by
  decide +kernel

theorem badOg : bindS false { CertificateChecks.KernelC690.CensSP.base with
    og := CertificateChecks.KernelC690.CensSP.og.reverse } = false := by decide +kernel

theorem badOmg : bindS false { CertificateChecks.KernelC690.CensSP.base with
    omg := CertificateChecks.KernelC690.CensSP.og } = false := by decide +kernel

theorem badKpg : bindS false { CertificateChecks.KernelC690.CensSP.base with
    kpg := CertificateChecks.KernelC690.CensSP.kpg.tail } = false := by decide +kernel

theorem badNS : bindS false { CertificateChecks.KernelC690.CensSP.base with nS := 1151 } =
    false := by decide +kernel

end CertificateChecks.KernelC690.CensSBind

end
