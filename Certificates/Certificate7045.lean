
module

public import CFSG.Quasithin.Recognition.RuRank3RuAutDataInputs
import Certificates.Kernel.SporSch.Ru.Glue7045

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native in
theorem certificate7045 :
    ((allLt 1755 fun j => ruCountOK j) = true)
    ∧ ((allLt 20 fun i => decide (CFSG.Quasithin.RuRank3.ruW[i]! < 1755) &&
         isInvA 4060 (ruTreeArr ruDArr[CFSG.Quasithin.RuRank3.ruW[i]!]!) ruWTI[i]!) = true ∧
       (allLt 4060 fun x => !(ruInS x) ||
         allLt x fun y => !(ruInS y) || ruFPArr[x]! != ruFPArr[y]!) = true)
    ∧ (orbCheck 1755 titsK0Gens = true ∧ labCount 1755 titsK0Lab titsK0Lab[0]! = 975 ∧
       (allLt 1755 fun j => titsK0Lab[j]! == titsK0Lab[0]! ||
         decide (labCount 1755 titsK0Lab titsK0Lab[j]! < 975)) = true ∧
       (allLt 1755 fun j => (titsK0Lab[j]! != titsK0Lab[0]!) == ruRowA ruTIG0 ruDArr[j]!) = true) := KernelSporSch.Glue7045.c7045

end Certificates
