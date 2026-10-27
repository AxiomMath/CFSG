
module

public import Certificates.Certificate2292Base

public import CFSG.Sporadic.SuzOddCore.CertChainCheckInputs
public meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Perm.Chain
import Certificates.Kernel.Sporadic.OddCore.Suz2292F

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native in
open CFSG.Perm.Native in
theorem certificate2292 : certArr 2 = certArr 0 ∧ certArr 3 = certArr 1 ∧
    (∀ j < 10, 2 ≤ j → eqA 22880 certStrongArrs[j]!
      (wordA 22880 certStrongArrs certStrongInvs certDerivs[j]!) = true) ∧
    (∀ i ≤ 6, levelIdx certStrongArrs certBaseNat.toArray i = certLevelIdx i) ∧
    (∀ i < 6, treeOK 22880 (certBaseNat.getD i 0) (certTree i) certLetters
      (certLevelLetters i) = true) ∧
    (∀ i < 6, (certTree i).pts.size = certOrbitSizes.getD i 0) ∧
    (∀ j < 10, ∀ x < 22880, (certStrongArrs[j]!)[x]! < 2 ^ 32 ∧ (certStrongInvs[j]!)[x]! < 2 ^ 32) ∧
    (∀ j < 10, certStrongInvs[j]!.size = 22880) := KernelSpor.OddCore.facts2292

end Certificates
