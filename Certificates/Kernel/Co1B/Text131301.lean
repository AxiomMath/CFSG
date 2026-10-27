module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.E27.Co1S0

public section

set_option maxRecDepth 400000 in
#ks_chars CertificateChecks.KernelCo1B.S0131301.OT CFSG.Sporadic.Co1.S0.opsStr

set_option maxRecDepth 400000 in
#ks_chars CertificateChecks.KernelCo1B.S0131301.PT CFSG.Sporadic.Co1.S0.parStr

set_option maxRecDepth 400000 in
#ks_chars CertificateChecks.KernelCo1B.S0131301.LT CFSG.Sporadic.Co1.S0.LStr

end
