module

public import Certificates.Data.CentLinesCo2
public import Certificates.Data.Kernel.CoreD2K.Steps

public section

namespace CertificateChecks.KernelCoreD2K.Co2Cent

open Certificates.CoreD2Perm CFSG.KS.CoreD2K

@[expose] def co2CentK : VData :=
  { co2CentLinesData with
    base := { co2CentLinesData.base with
      gWs := keepWs [0, 1, 6, 7] 0 co2CentLinesData.base.gWs } }

@[expose] def co2CentReps : List Nat := [4]

@[expose] def co2CentSteps : List CStep :=
  [⟨2, 4, 0, 3, 3⟩, ⟨5, 4, 1, 4, 4⟩, ⟨0, 2, 0, 2, 2⟩, ⟨1, 5, 0, 2, 1⟩, ⟨3, 0, 1, 0, 1⟩]

end CertificateChecks.KernelCoreD2K.Co2Cent

end
