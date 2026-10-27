
module

public import Certificates.Certificate3148Base
import all Certificates.Certificate3148Base

public import CFSG.Monster.B.Fischer.Fi22CentralizerCheckInputs
import Certificates.Kernel.Sporadic.Fi22.C3148

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate3148 : ((fi22OuterStrong3510 1)[0]!)[0]! = 0 ∧
      (∀ k < 3, eqA 3510 (compA 3510 (fi22OuterStrong3510 1)[0]! (fi22OuterStrong3510 3)[k]!)
        (compA 3510 (fi22OuterStrong3510 3)[k]! (fi22OuterStrong3510 1)[0]!) = true) ∧
      translatesOK fi22OrigArrs (fixedList 3510 (fi22OuterStrong3510 6)[0]!) fi22FixOrbit0.1
        fi22FixOrbit0.2.1 fi22FixOrbit0.2.2 = true ∧
      fi22FixOrbit0.1.toList.Nodup ∧ fi22FixOrbit0.1.size = 3511 ∧
      translatesOK fi22OrigArrs (fixedList 3510 (fi22OuterStrong3510 6)[1]!) fi22FixOrbit1.1
        fi22FixOrbit1.2.1 fi22FixOrbit1.2.2 = true ∧
      fi22FixOrbit1.1.toList.Nodup ∧ fi22FixOrbit1.1.size = 3511 ∧
      translatesOK fi22OrigArrs (fixedList 3510 (fi22OuterStrong3510 1)[0]!) fi22FixOrbitZ.1
        fi22FixOrbitZ.2.1 fi22FixOrbitZ.2.2 = true ∧
      fi22FixOrbitZ.1.toList.Nodup ∧ fi22FixOrbitZ.1.size = 3510 := KernelSpor.Fi22C3148.facts

end Certificates
