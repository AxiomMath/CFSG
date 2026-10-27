module

public import CFSG.RankThree.PartOne.S11c.HNInvPairInputs
public meta import CFSG.Sporadic.HNOddCore.SixCheckInputs
public meta import CFSG.Sporadic.HNOddCore.ChainUtil
public meta import CFSG.RankThree.Native.HSMcLSmallData
import Certificates.Kernel.Sporadic.OddCore.HNPair

public section

namespace Certificates

open CertificateChecks

theorem certificate14981 : CFSG.RankThree.PartOne.HNRed.Native.pairCheck = true := KernelSpor.HNPair.pair_ok

end Certificates
