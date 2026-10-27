module

public import CFSG.Sporadic.HNSchreier.RankCheckInputs
public meta import CFSG.Sporadic.HNSchreier.InvolCheck
public meta import CFSG.Sporadic.HNSchreier.RankData
public meta import CFSG.Sporadic.HNSchreier.FAData
public import Certificates.Kernel.SporSch.HN.Rank2105

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native in
open CFSG.Sporadic.He.Native CFSG.ONSchreier.Native in
theorem certificate2105 : rankChecks rowsA rowsB rankCertRows = true := KernelSporSch.HNRank.facts

end Certificates
