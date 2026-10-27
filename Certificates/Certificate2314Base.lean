
module

public import CFSG.Sporadic.ThSchreier.NoTransvectionInputs
public meta import CFSG.Sporadic.ThSchreier.RigidityBase
import CFSG.Sporadic.ThSchreier.AutCoreBase
meta import CFSG.Sporadic.ThSchreier.NoTransvectionInputs

@[expose] public section

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open CFSG.Certificates Equiv Equiv.Perm Matrix

namespace CertificateChecks.Batch2314

private theorem dtCols_eq_0 : posWord8 B1enc B2enc dtWord = dtCols := by
  decide +kernel

end CertificateChecks.Batch2314

namespace Certificates

end Certificates
