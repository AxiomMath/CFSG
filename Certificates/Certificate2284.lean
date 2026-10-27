module

public import CFSG.Sporadic.SmallOddCore.McLCheckInputs
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
import Certificates.Kernel.Sporadic.OddCore.MNF

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native in
theorem certificate2284 : (mclStabOK = true)
    ∧ (centDataOK 275 898128000 120000 mclPGTbls mclPGInvTbls mclSift mclOuterTbl mclSylowGenTbls
      mclSylowOrder mclRows = true
    ) := KernelSpor.MNd.facts2284

end Certificates
