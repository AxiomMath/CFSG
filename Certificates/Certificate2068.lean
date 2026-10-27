
module

public import Certificates.Certificate2068Base
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckBase
import Certificates.Kernel.Sporadic.Fi22.C2068Base
meta import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckBase
meta import CFSG.Monster.B.Fischer.Fi22GraphCheckBase

public import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
public meta import Certificates.Data.CFSGNative.FischerOddCore.Checks
import Certificates.Kernel.Sporadic.Fi22.C2068
import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
meta import CFSG.Sporadic.FischerOddCore.Fi22ExtData
meta import CFSG.Monster.B.Fischer.Fi22OuterCheck
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs
meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheck
meta import CFSG.Monster.B.Fischer.Fi22CoverCheckBase
meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
meta import CFSG.Monster.B.Fischer.Fi22GraphCheck
import CFSG.Monster.B.Fischer.PinnedChainInputs
import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
import CFSG.Monster.B.Fischer.Fi22OuterArrays
import CFSG.Monster.B.Fischer.Fi22OrderCheck

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore.Native in
theorem certificate2068 : labelOKRes 256 262144 fi22TLevels fi22ExtQArr fi22ExtQiArr fi22ExtVArr fi22ExtDArr
      fi22ExtPosArr fi22ExtSteps fi22ExtStepsInv fi22ExtRoots fi22ExtLabels 4 = true ∧
    (∀ j < 79, fi22ExtRoots[j]! < 262144 ∧ fi22ExtLabels.lab[fi22ExtRoots[j]!]! = j) ∧
    (∀ j < 79, labCount fi22ExtLabels.lab 262144 j = fi22ExtClassSizes.getD j 0) ∧
    (∀ j < 79, eqA 3510 (fi22ExtFullArr fi22ExtRoots[j]!) (fi22ExtArr (27 + j)) = true) ∧
    (∀ k < 10, isInvA 256 fi22ExtSteps[k]! fi22ExtStepsInv[k]! = true) ∧
    (∀ j < 79, fi22InP (fi22ExtArr (106 + j)) = true ∧
      eqA 3510 (compA 3510 (fi22ExtArr (106 + j)) (fi22ExtArr (27 + j)))
        (compA 3510 (fi22ExtArr (21 + fi22ExtGlobalClasses.getD j 0)) (fi22ExtArr (106 + j))) =
        true) ∧
    (∀ i < 3, eqA 3510 (fi22ExtArr (21 + i)) (fi22OuterStrong3510 6)[i]! = true) ∧
    eqA 3510 (fi22ExtArr 24) fi22GraphOuterArr = true ∧
    (∀ k < 6, isInvArr 3510 (fi22ExtArr (21 + k)) = true) ∧
    ((List.range 6).map fun k => fixCount 3510 (fi22ExtArr (21 + k))) =
      [54, 182, 694, 72, 360, 64] ∧
    (∀ k < 3, fi22InP (fi22ExtArr (21 + k)) = true) ∧
    (∀ k < 3, fi22InP (fi22ExtArr (24 + k)) = false ∧
      fi22InP (compA 3510 fi22GraphOuterArr (fi22ExtArr (24 + k))) = true) ∧
    labelledCount fi22ExtLabels.lab 262144 79 = 6143 := KernelSpor.Fi22LabA.facts

end Certificates
