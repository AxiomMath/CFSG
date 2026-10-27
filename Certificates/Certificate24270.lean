module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.M12Inputs
import all Init.Data.Nat.Fold

public section

namespace CertificateChecks.Batch24270

private theorem e8Data_0 : CFSG.EvenSporadicStandard.HypOne.M12.e8Data = true := by
  decide +kernel

private theorem foursData_1 : CFSG.EvenSporadicStandard.HypOne.M12.foursData = true := by
  decide +kernel

end CertificateChecks.Batch24270

namespace Certificates

open CertificateChecks

theorem certificate24270 : (CFSG.EvenSporadicStandard.HypOne.M12.e8Data = true) ∧
    (CFSG.EvenSporadicStandard.HypOne.M12.foursData = true) := by
  exact ⟨CertificateChecks.Batch24270.e8Data_0, CertificateChecks.Batch24270.foursData_1⟩

end Certificates
