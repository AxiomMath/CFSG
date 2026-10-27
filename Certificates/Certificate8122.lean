module

public import CFSG.RankThree.Native.Co3FiveArrays
public import CFSG.RankThree.Native.ChainCentralizer
public import CFSG.Sporadic.Schreier.Co3OrderCheck
public import CFSG.Monster.B.Mathieu.SylowCore
public import CFSG.RankThree.Native.Co3FiveCheckInputs
import Certificates.Kernel.Co3Five.Facts

public section

namespace Certificates

open CertificateChecks.KernelCo3Five in
open CFSG CFSG.RankThree CFSG.RankThree.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Schreier.Co3 in
theorem certificate8122 : (co3FiveChainCheck (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3FiveC25Cert = true)
    ∧ (co3FiveQCheck co3FiveQCert co3FiveLines = true)
    ∧ (co3FiveC25Check co3FiveC25Cert co3FiveQCert = true)
    ∧ (co3FiveC0Check co3FiveC0GenArrs co3FiveDGenArrs co3FiveC0Cert co3FiveDCert = true) := ⟨chain_ok, q_ok, c25_ok, c0_ok⟩

end Certificates
