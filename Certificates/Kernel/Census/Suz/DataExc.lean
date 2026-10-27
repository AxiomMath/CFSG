module

public import Certificates.Kernel.Census.Suz.Data
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.KC.Census in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.Suz
  "Certificates/Kernel/Census/Suz/data/suzExc.json.gz" 1749657 2357406781495629297
  (suzWitsExc : Array WitP) (suzExcsExc : List ExcRefP)

public section

namespace CertificateChecks.KernelCensus.Suz

open CFSG.KC.Census

@[expose] noncomputable def nodesExc : Array NodeP :=
  Array.mk ((suzBases.toList.zip suzWitsExc.toList).map fun bw => ⟨bw.1, bw.2, #[]⟩)

@[expose] noncomputable def conjExc : ConjDataP :=
  ⟨suzXs, suzRs, suzCjs, suzBs, suzUs, suzIm, suzWt, suzCm, suzCs, suzCi, suzRoots, nodesExc,
    suzEnts, #[], suzExcsExc⟩

end CertificateChecks.KernelCensus.Suz

end
