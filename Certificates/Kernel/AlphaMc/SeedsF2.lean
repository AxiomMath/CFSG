module

public import Certificates.Kernel.LocalComp.M1Gen
import all CFSG.Blueprint.NativeSporadic
meta import CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelAM.C1A CFSG.Blueprint.NativeSporadic.Co1Seed1
#lc_m1 CertificateChecks.KernelAM.C1A CFSG.Blueprint.NativeSporadic.Co1Seed1 24
#ks_chars CertificateChecks.KernelAM.C1B CFSG.Blueprint.NativeSporadic.Co1Seed2
#lc_m1 CertificateChecks.KernelAM.C1B CFSG.Blueprint.NativeSporadic.Co1Seed2 24
#ks_chars CertificateChecks.KernelAM.C2A CFSG.Blueprint.NativeSporadic.Co2Seed1
#lc_m1 CertificateChecks.KernelAM.C2A CFSG.Blueprint.NativeSporadic.Co2Seed1 22
#ks_chars CertificateChecks.KernelAM.C2B CFSG.Blueprint.NativeSporadic.Co2Seed2
#lc_m1 CertificateChecks.KernelAM.C2B CFSG.Blueprint.NativeSporadic.Co2Seed2 22
#ks_chars CertificateChecks.KernelAM.C3A CFSG.Blueprint.NativeSporadic.Co3Seed1
#lc_m1 CertificateChecks.KernelAM.C3A CFSG.Blueprint.NativeSporadic.Co3Seed1 22
#ks_chars CertificateChecks.KernelAM.C3B CFSG.Blueprint.NativeSporadic.Co3Seed2
#lc_m1 CertificateChecks.KernelAM.C3B CFSG.Blueprint.NativeSporadic.Co3Seed2 22

end
