
module

public import Certificates.Certificate8132Base

public import CFSG.RankThree.Native.LyOperatorData
public import CFSG.RankThree.Native.LySeedCheckInputs
import Certificates.Kernel.SporSch.Ly.Seed8132

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native in
theorem certificate8132 : lySeedChecks = true := KernelSporSch.LySd.facts

end Certificates
