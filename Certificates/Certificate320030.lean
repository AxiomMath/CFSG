module

public import Certificates.Data.A5GL42
import Certificates.Kernel.Misc.GL4.A5Klein

public section

namespace Certificates

open CertificateChecks.KernelMisc.GL4A5 in
theorem certificate320030 : A5GL42.Facts :=
  ⟨subspaces_complete, classify, groupN, groupO, gens, fixN, fixO, kleinN, kleinO⟩

end Certificates
