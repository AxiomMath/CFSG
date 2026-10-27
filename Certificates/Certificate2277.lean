module

public import CFSG.Sporadic.SmallOddCore.J2CentralizerDInputs
public meta import CFSG.Sporadic.SmallOddCore.J2LocalCheck
public meta import CFSG.Sporadic.Schreier.PairJ2Check
import Certificates.Kernel.Sporadic.OddCore.J2D2277
import Certificates.Kernel.Sporadic.OddCore.J2D2277Neg

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SmallOddCore Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative in
open CFSG.Certificates CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate2277 : countW (commW 315 (j2DGens.map natArr)) PairJ2.blocks [] = 12 := KernelSpor.J2DCnt.facts2277

end Certificates
