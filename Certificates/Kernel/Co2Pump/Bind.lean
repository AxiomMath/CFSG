module

public import Certificates.Kernel.Co2Pump.Data
public import Certificates.Kernel.Co2Pump.Src
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Sporadic.Co2Cert.Data
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.Co2Pump.Data
meta import Certificates.Kernel.Co2Pump.Src
meta import CFSG.Sporadic.Co2Cert.Data

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelCo2Pump.PT CFSG.HardMathSupport.Solomon.Coordinator.Co2Pump.pumpText
#kmisc_packarrs CertificateChecks.KernelCo2Pump.PR CertificateChecks.KernelCo2Pump.pumpRows 12
#kmisc_packarrs CertificateChecks.KernelCo2Pump.OA CFSG.Sporadic.Co2Cert.co2OrigArrs 12
#kmisc_packarrs CertificateChecks.KernelCo2Pump.PMt CertificateChecks.KernelCo2Pump.PMtArr 484
#kmisc_packarrs CertificateChecks.KernelCo2Pump.DMt CertificateChecks.KernelCo2Pump.DMtArr 484
#kmisc_packarrs CertificateChecks.KernelCo2Pump.PAM CertificateChecks.KernelCo2Pump.PAMtArr 484
#kmisc_packarrs CertificateChecks.KernelCo2Pump.PAI CertificateChecks.KernelCo2Pump.PAItArr 12
#kmisc_packarrs CertificateChecks.KernelCo2Pump.PBM CertificateChecks.KernelCo2Pump.PBMtArr 484
#kmisc_packarrs CertificateChecks.KernelCo2Pump.PBI CertificateChecks.KernelCo2Pump.PBItArr 12
