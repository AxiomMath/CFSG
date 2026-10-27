
module

public import Certificates.Certificate2067Base

public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtData
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import Certificates.Kernel.Sporadic.Fi22.E2067

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Co2.Native in
open CFSG.Monster.B.Fischer in
theorem certificate2067 : layoutOK fi22ExtBytes3510 3 3510 185 = true ∧ layoutOK fi22ExtBytes256 2 256 18 = true ∧
    (∀ L < 185, isInvA 3510 (fi22ExtArr L) (invCand 3510 (fi22ExtArr L)) = true) ∧
    (∀ L < 18, isInvA 256 (fi22ExtArr256 L) (invCand 256 (fi22ExtArr256 L)) = true) ∧
    (∀ x ∈ fi22ExtSmallPointsNat, x < 3510) ∧ fi22ExtSmallPointsNat.Nodup ∧
    fi22ExtSmallPointsNat.length = 256 ∧ (∀ c ∈ fi22ExtGlobalClasses, c < 6) ∧
    fi22ExtGlobalClasses.length = 79 ∧ fi22ExtClassSizes.length = 79 ∧
    wordsOK fi22ExtSmallGenCount 18 fi22ExtSmallDerivations = true := KernelSpor.Fi22E2067.facts2067

end Certificates
