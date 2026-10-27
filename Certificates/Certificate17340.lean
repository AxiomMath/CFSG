
module

public import Certificates.Data.TabFi23C
public meta import Certificates.Data.TabFi23C
import Certificates.Data.CFSGNative.Fi23.Certificate
import CFSG.Sporadic.Presentation.Fi23Inputs
import CFSG.Sporadic.Fi23.Simple
import CFSG.Sporadic.Bridge.Common
import CFSG.Sporadic.Presentation.Fi23
import Certificates.Data.CFSGNative.Bridge.Fi23GPL
import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Reps
import Certificates.Kernel.Fi23Tw.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi23.Native CFSG.HardMathSupport.Dickson.I271.TabFi23C in
theorem certificate17340 : fi23COK (orbitData ()) = true :=
  KernelFi23Tw.fi23C_ok

end Certificates
