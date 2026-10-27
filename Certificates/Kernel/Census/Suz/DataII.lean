module

public import Certificates.Kernel.Census.Suz.Data
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.KC.Census in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.Suz
  "Certificates/Kernel/Census/Suz/data/suzII.json.gz" 1714196 3613417909577676188
  (suzWitsII : Array WitP)

public section

namespace CertificateChecks.KernelCensus.Suz

open CFSG.KC.Census

@[expose] noncomputable def nodesII : Array NodeP :=
  Array.mk ((suzBases.toList.zip suzWitsII.toList).map fun bw => ⟨bw.1, bw.2, #[]⟩)

@[expose] noncomputable def conjII : ConjDataP :=
  ⟨suzXs, suzRs, suzCjs, suzBs, suzUs, suzIm, suzWt, suzCm, suzCs, suzCi, suzRoots, nodesII,
    suzEnts, #[], []⟩

end CertificateChecks.KernelCensus.Suz

end
