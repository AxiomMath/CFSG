
module

public import Certificates.Certificate2314Base
import all Certificates.Certificate2314Base

public import CFSG.Sporadic.ThSchreier.NoTransvectionInputs
public meta import CFSG.Sporadic.ThSchreier.RigidityBase
import CFSG.Sporadic.ThSchreier.AutCoreBase
meta import CFSG.Sporadic.ThSchreier.NoTransvectionInputs

public section

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open CFSG.Certificates Equiv Equiv.Perm Matrix

namespace CertificateChecks.Batch2314

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open CFSG.Certificates Equiv Equiv.Perm Matrix

end CertificateChecks.Batch2314

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 in
open CFSG.Certificates Equiv Equiv.Perm Matrix in
theorem certificate2314 : posWord8 B1enc B2enc dtWord = dtCols := by
  exact CertificateChecks.Batch2314.dtCols_eq_0

end Certificates
