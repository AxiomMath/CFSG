module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.GrSLitL34FactsCF23HeCheck
meta import Certificates.Data.GrSLitL34FactsCF23HeCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.HeJ

open CFSG.QuasithinUnique.Setup.X1 CFSG.ComponentClassification.GSThmB.CF23L34

meta def tabsM : Array (Array Nat) :=
  (([1, 2, 32, 86, 103, 173, 216, 217, 226, 227, 250, 277, 278, 279, 280, 281, 282] : List ℤ).flatMap
    fun r =>
    [(pLetter 8330 hjRegs r).1, (pLetter 8330 hjRegs r).2]).toArray

end CertificateChecks.KernelLC.HeJ

#kmisc_packarrs CertificateChecks.KernelLC.HeJT CertificateChecks.KernelLC.HeJ.tabsM 14

end
