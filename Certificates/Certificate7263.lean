module

public import Certificates.Data.CoverBSignedMcL
public import Certificates.Data.CFSGNative.SectionRank.F3
import CFSG.Certificates.Kernel.OpsLaySignedSound
import Certificates.Kernel.OpsLaySigned.McL

public section

open CertificateChecks.KernelFusLay CertificateChecks.KernelOpsLaySigned

namespace Certificates

open CFSG.SectionRank.QTK.CoverB CFSG.SectionRank.Native in
theorem certificate7263 : SignedData.check (ops3 21) mclSigned = true :=
  CFSG.KC.OpsLaySigned.signedK_sound McL.lay_ok rfl rfl McL.decA McL.decB McL.signed7263_seedA
    McL.signed7263_seedB McL.signed7263_K

end Certificates
