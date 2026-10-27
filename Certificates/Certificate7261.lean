module

public import Certificates.Data.CoverBSignedON
public import Certificates.Data.CFSGNative.SectionRank.F3
import CFSG.Certificates.Kernel.OpsLaySignedSound
import Certificates.Kernel.OpsLaySigned.ON

public section

open CertificateChecks.KernelFusLay CertificateChecks.KernelOpsLaySigned

namespace Certificates

open CFSG.SectionRank.QTK.CoverB CFSG.SectionRank.Native in
theorem certificate7261 : SignedData.check (ops3 154) onSigned = true :=
  CFSG.KC.OpsLaySigned.signedK_sound ON.lay_ok rfl rfl ON.decA ON.decB ON.signed7261_seedA
    ON.signed7261_seedB ON.signed7261_K

end Certificates
