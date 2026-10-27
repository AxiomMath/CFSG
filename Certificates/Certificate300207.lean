module

public import CFSG.Quasithin.Background.Harris.R1.D4ModelCheck
import Certificates.Kernel.D4QK.C300207

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.Background.Harris.R1.D4Vert in
theorem certificate300207 :
    fixLine (nWords.getD 4 []) = true
    ∧ movePt (nWords.getD 4 []) = true
    ∧ fixPt (hWords.getD 2 []) = true
    ∧ fixPt (hWords.getD 3 []) = true
    ∧ x0IsVB = true
    ∧ zetaConjOK = true
    ∧ vCommOK = true
    ∧ r0NotComm = true
    ∧ centerCheck tQ = true
    ∧ kcCheck tK = true
    ∧ bTabOK = true
    ∧ sInQ2 = true
    ∧ sTabOK = true := KernelD4Q.C300207.cert

end Certificates
