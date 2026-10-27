
module

public import Certificates.Certificate2180Base

public import CFSG.Sporadic.Schreier.J4SRankData
public meta import CFSG.Sporadic.Schreier.J4SRankData
import Certificates.Kernel.SporSch.J4S.RankP

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier in
theorem certificate2180 : (rows3OK (etaP 1).1 = true ∧ rows3OK (etaP 14).1 = true)
    ∧ (q3RowsOK Q3GenPairs = true) := KernelSporSch.J4Rank.facts

end Certificates
