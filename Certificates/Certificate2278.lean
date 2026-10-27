
module

public import Certificates.Certificate2278Base

public import CFSG.Sporadic.SmallOddCore.J2CheckInputs
public meta import CFSG.Sporadic.SmallOddCore.J2Data
public meta import CFSG.Sporadic.Schreier.PairJ2Check
import Certificates.Kernel.Sporadic.OddCore.J2CnF

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative in
open CFSG.Monster.B.Co2.Native in
theorem certificate2278 : (j2StabOK = true)
    ∧ (centDataOK 315 604800 3000 j2PGTbls j2PGInvTbls j2Sift j2OuterTbl j2SylowGenTbls j2SylowOrder
      j2Rows = true
    ) := KernelSpor.J2Cn.facts2278

end Certificates
