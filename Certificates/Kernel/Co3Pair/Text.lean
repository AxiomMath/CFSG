module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.TextSound
public import Certificates.Data.Co3Pump
meta import Certificates.Data.Co3Pump
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelCo3Pair.PT CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump.pumpText

@[expose] noncomputable def CertificateChecks.KernelCo3Pair.PTN.chars : List Char :=
  CertificateChecks.KernelCo3Pair.PT.chars ++ ['\n']

#ks_hexlines CertificateChecks.KernelCo3Pair.PTN
  CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump.pumpText 3 276 9

end
