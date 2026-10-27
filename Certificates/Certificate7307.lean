module

public import CFSG.Quasithin.Recognition.RuRank3J55DataInputs
import Certificates.Kernel.SporSch.Ru.Q7307

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native in
theorem certificate7307 :
    (allLt 1755 fun j => titsBallArr[j]! == (j == 0 || ruRowA ruTI1 ruDArr[j]!)) = true := KernelSporSch.Q7307.c7307

end Certificates
