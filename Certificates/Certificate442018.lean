module

public import Certificates.Data.OmegaCYFacts
import Certificates.Certificate2012
import Certificates.Certificate23100
import Certificates.Certificate442002
import Certificates.Kernel.OmegaCY.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate442018 : OmegaCY.Facts :=
  fun _ _ _ _ hT0 hTA hT2 ⟨_, hw, hw0⟩ hM hB0 hB0c hB0n _ _ Φ hΦ α hα _ _ hΦt hΦz hαt hαz hrange
    h02 h20 => KernelA45.lemmaY_of_model hT0 hTA hT2 hw hw0 hM hB0 hB0c hB0n Φ hΦ α hα hΦt hΦz
      hαt hαz hrange h02 h20

end Certificates
