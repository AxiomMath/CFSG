module

public import Certificates.Data.Th687.AutD
import Certificates.Kernel.Th.AutD.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Th.Recog CFSG.PSL3Four.Native in
theorem certificate687009 :
    piCheck () = true ∧
      iotaCheck () = true ∧
      partnerCheck () = true ∧
      hGenCheck () = true ∧
      CFSG.PSL3Four.Native.invsOK 51 (dEnum ()).tabs (dEnumInv ()) = true ∧
      cover24Check () = true ∧
      autCheck () = true := KernelTh.AutD.autD_true

end Certificates
