module

public import Certificates.Data.CentLinesRu
public import Certificates.Data.Kernel.CoreD2K.Steps

public section

namespace CertificateChecks.KernelCoreD2K.RuCent

open Certificates.CoreD2Perm CFSG.KS.CoreD2K

@[expose] def ruCentK : VData :=
  { ruCentLinesData with
    base := { ruCentLinesData.base with
      gWs := keepWs [0, 1, 2, 3, 6, 8] 0 ruCentLinesData.base.gWs } }

@[expose] def ruCentReps : List Nat := [0, 3, 5]

@[expose] def ruCentSteps : List CStep :=
  [⟨1, 0, 0, 2, 1⟩, ⟨2, 5, 0, 1, 4⟩, ⟨4, 3, 1, 2, 1⟩]

end CertificateChecks.KernelCoreD2K.RuCent

end
