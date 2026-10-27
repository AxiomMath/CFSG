module

public import CFSG.Sporadic.SuzOddCore.ThreeLocalCheckInputs
public meta import CFSG.Sporadic.SuzOddCore.GammaCheck
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.Schreier.Check
import Certificates.Kernel.Sporadic.OddCore.Suz2308

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.PSL3Four.Native in
theorem certificate2308 : threeChecks fullExtArrs (tFullOf fullExtArrs) (compactEnum (tFullOf fullExtArrs)) = true := KernelSpor.OddCore.S2308.facts2308

end Certificates
