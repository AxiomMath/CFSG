
module

public import Certificates.Certificate2322Base

public import CFSG.Sporadic.ThSchreier.RowInputs
public meta import Certificates.Data.CFSGNative.Th.Base
import Certificates.Kernel.SporSch.Th.Row2322

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Th.Max3 Matrix Pointwise in
theorem certificate2322 : eqRows (mulRows fcRows formInvRows) idRows = true ∧
    eqRows (mulRows formInvRows fcRows) idRows = true := KernelSporSch.ThRow.facts

end Certificates
