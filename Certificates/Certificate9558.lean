module

public import Certificates.Data.ONanG28OmFacts
import Certificates.Kernel.CertF8.Glue9558

public section

namespace Certificates

open CFSG.AGLEmbedding.KFactProofs.G28 in
theorem certificate9558 : ∃ D : OmCodes, D.OK := ⟨_, CFSG.KC.CertF8.Om9558.om9558OK⟩

end Certificates
