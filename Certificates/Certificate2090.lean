module

public import CFSG.Sporadic.HNOddCore.RkCheckInputs
public meta import CFSG.Sporadic.HNSchreier.RankCheck
public meta import CFSG.Sporadic.HNOddCore.RankData
public meta import CFSG.Sporadic.HNOddCore.InvData
import Certificates.Kernel.Sporadic.OddCore.HN2090

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native in
open CFSG.Sporadic.He.Native CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier in
open CFSG.Sporadic.HNSchreier.Native in
theorem certificate2090 : invRankChecks rowsA rowsB invRankRows = true := KernelSpor.HN2090.facts2090

end Certificates
