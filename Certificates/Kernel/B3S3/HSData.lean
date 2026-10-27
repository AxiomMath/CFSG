module

public import Certificates.Data.B3Spor3.HS
public import Certificates.Kernel.B3S3.HexGen
public import Certificates.Kernel.Sporadic.RawGenSplit
public meta import Certificates.Data.B3Spor3.HS

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelB3S3.HS

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3

@[expose] def d0 : List (List ℤ) := hsS3C0W.toList.drop 2

end CertificateChecks.KernelB3S3.HS

end

set_option Elab.async false

#ks_chars CertificateChecks.KernelB3S3.HS.QG CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3QGensHex
#kb3_hexarrs CertificateChecks.KernelB3S3.HS.QG
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3QGensHex 3 3850 12
#ks_chars CertificateChecks.KernelB3S3.HS.LX CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3LinesHex
#kb3_hexarrs CertificateChecks.KernelB3S3.HS.LX
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3LinesHex 3 3850 12
#ks_chars CertificateChecks.KernelB3S3.HS.H CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3TransHex
#kb3_hexarrs CertificateChecks.KernelB3S3.HS.H
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3TransHex 3 3850 12
#ks_chars CertificateChecks.KernelB3S3.HS.XC CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3CaseXHex
#kb3_hexarrs CertificateChecks.KernelB3S3.HS.XC
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3CaseXHex 3 3850 12
#ks_chars CertificateChecks.KernelB3S3.HS.SS CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3C0SHex
#kb3_hexarrs CertificateChecks.KernelB3S3.HS.SS
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3C0SHex 3 3850 12
#ks_chars CertificateChecks.KernelB3S3.HS.GG
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3C0GensHex
#kb3_hexarrs CertificateChecks.KernelB3S3.HS.GG
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3C0GensHex 3 3850 12

#ks_rawchain_sl2_data CertificateChecks.KernelB3S3.HS.C0 3850 12 0 64
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3C0S
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3C0Base 2 CertificateChecks.KernelB3S3.HS.d0
