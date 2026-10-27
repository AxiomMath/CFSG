module

public import CFSG.Quasithin.Recognition.RuRank3TitsSylInputs
import Certificates.Kernel.SporSch.Tits.Glue7051

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates in
theorem certificate7051 :
    orbCheck 1755 titsPAGens = true ∧ CFSG.Quasithin.RuRank3.labCount 1755 titsPALab titsPALab[0]! = 1 ∧
      titsPALab[1]! = titsPALab[2]! ∧ CFSG.Quasithin.RuRank3.labCount 1755 titsPALab titsPALab[1]! = 2 ∧
      (allLt 1755 fun x => x == 0 || x == 1 || x == 2 ||
        decide (8 ≤ CFSG.Quasithin.RuRank3.labCount 1755 titsPALab titsPALab[x]!)) = true ∧
      (titsGenArrs[1]!)[0]! = 0 := KernelSporSch.Glue7051.c7051

end Certificates
