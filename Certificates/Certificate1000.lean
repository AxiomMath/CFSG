
module

public import Certificates.Certificate1000Base

public import Certificates.Data.CFSGNative.Fischer.Xi22
import Certificates.Kernel.Misc.LinesBridge
import Certificates.Kernel.Misc.FischerDelta
import Certificates.Kernel.Misc.HypBridge
import Certificates.Kernel.Misc.XiBridge

public section

namespace Certificates

open CFSG CFSG.Fischer CFSG.Fischer.Native in
theorem certificate1000 : (
 polarLinesCertificate () = true 
)
    ∧ (
 deltaCertificate () = true 
)
    ∧ (
 hypCertificate () = true 
)
    ∧ (
 xiCertificate () = true 
) :=
  ⟨CFSG.KD.Misc.Lines.polarLines_true, CFSG.KD.Misc.Polar.delta_true,
    CFSG.KD.Misc.Hyp.hyp_true, CFSG.KD.Misc.Xi.xi_true⟩

end Certificates
