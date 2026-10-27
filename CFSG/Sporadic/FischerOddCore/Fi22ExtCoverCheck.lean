
module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverCheckBase

public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
public import Certificates.Data.CFSGNative.FischerOddCore.Checks
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
public meta import Certificates.Data.CFSGNative.FischerOddCore.Checks
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverCheckInputs
public import Certificates.Certificate2068

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore.Native

theorem fi22ExtCover_check :
    labelOKRes 256 262144 fi22TLevels fi22ExtQArr fi22ExtQiArr fi22ExtVArr fi22ExtDArr
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
    labelledCount fi22ExtLabels.lab 262144 79 = 6143 :=
  Certificates.certificate2068

end CFSG.Sporadic.FischerOddCore
