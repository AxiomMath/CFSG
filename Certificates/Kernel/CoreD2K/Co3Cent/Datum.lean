module

public import Certificates.Data.CentLinesCo3
public import Certificates.Data.Kernel.CoreD2K.Steps

public section

namespace CertificateChecks.KernelCoreD2K.Co3Cent

open Certificates.CoreD2Perm CFSG.KS.CoreD2K

@[expose] def co3CentK : VData :=
  { co3CentLinesData with
    base := { co3CentLinesData.base with
      gWs := keepWs [0, 1, 2, 3, 4, 6, 8] 0 co3CentLinesData.base.gWs } }

@[expose] def co3CentReps : List Nat := [1, 3]

@[expose] def co3CentSteps : List CStep :=
  [⟨4, 1, 2, 4, 1⟩, ⟨0, 4, 4, 2, 3⟩, ⟨2, 3, 2, 0, 2⟩, ⟨5, 3, 4, 3, 4⟩]

end CertificateChecks.KernelCoreD2K.Co3Cent

end
