
module

public import Certificates.Certificate2311Base
public import CFSG.Sporadic.ThSchreier.GlobalDataBase
public import CFSG.Sporadic.Th.SimpleBase
public meta import CFSG.Sporadic.ThSchreier.RowBase
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase
import Certificates.Kernel.SporSch.Th.Key2311Base

public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.Th.SimpleBase1
public meta import CFSG.Sporadic.ThSchreier.Row
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
import Certificates.Kernel.SporSch.Th.Key2311
public import CFSG.Sporadic.Th.LocalBase1
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Th.Max3 Pointwise in
theorem certificate2311 : rowKeyOf wKey = wKeyRow := KernelSporSch.ThKey.facts

end Certificates
