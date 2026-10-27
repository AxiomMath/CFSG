module

public import Certificates.Data.TabFi23Y
public meta import Certificates.Data.TabFi23Y
import Certificates.Data.CFSGNative.Fi23.Certificate
import CFSG.Sporadic.Presentation.Fi23Inputs
import CFSG.Sporadic.Fi23.Simple
import CFSG.Sporadic.Bridge.Common
import CFSG.Sporadic.Presentation.Fi23
import Certificates.Data.CFSGNative.Bridge.Fi23GPL
import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.Fi23Y322.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi23.Native CFSG.HardMathSupport.Dickson.I271.TabFi23Y in
theorem certificate17339 : fi23YOK (orbitData ()) = true :=
  KernelFi23Y322.yCheck_ok

end Certificates
