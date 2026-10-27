
module

public import CFSG.Quasithin.Recognition.RuRank3RuIsoDataInputs
import Certificates.Kernel.SporSch.Ru.Iso7047

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native in
theorem certificate7047 :
    (allLt 4060 fun x => lettersOK 2 (ruTreeWord x) && (ruTreeArr x)[0]! == x) = true ∧
      (allLt 4 fun i => isInvA 4060 (ruR0Arr i) (invCand 4060 (ruR0Arr i)) &&
        ruSift 4060 (ruField4060 3) ruJoinBase (ruR0Arr i) && (ruR0Arr i)[0]! == 0 &&
        allLt 1755 fun j => (ruR0Arr i)[ruDArr[j]!]! == ruDArr[(titsGenArrs[i]!)[j]!]!) = true ∧
      (allLt 1755 fun j => decide (ruDArr[j]! < 4060) && ruDArr[j]! != 0) = true ∧
      (allLt 1755 fun j => allLt j fun j' => ruDArr[j]! != ruDArr[j']!) = true ∧
      ruDArr[0]! = 1 := KernelSporSch.Iso7047.c7047

end Certificates
