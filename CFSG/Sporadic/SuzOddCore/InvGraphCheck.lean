
module

public import CFSG.Sporadic.SuzOddCore.InvGraphCheckBase

public import CFSG.Sporadic.SuzOddCore.InvArraysCheck
public import Certificates.Data.CFSGNative.Schreier.Refine
public import Mathlib.Data.Fintype.Card
public meta import CFSG.Sporadic.SuzOddCore.InvArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Refine
public meta import Mathlib.Data.Fintype.Card
public import CFSG.Sporadic.SuzOddCore.InvGraphCheckInputs
public import Certificates.Certificate2301

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem invGraph_check :
    adjOK 1782 #[b0Arr, b1Arr] invNbr invNeighbors = true ∧
    (∀ x < 1782, invNbr[vArr[x]!]! = imgSorted vArr invNbr[x]!) ∧
    (∀ x < 1782, (invNbr[x]!).length = 416) ∧
    (∀ i < 4, tArr i = invRepArr i) ∧
    (∀ i < 4, ∀ s < (invSteps.getD i []).length,
      classCount (stageColour i s) ((stepPoints i).getD s 0) ≤
        ((invSteps.getD i []).getD s []).getD 1 0) ∧
    (∀ i < 4, ((stageColour i (invSteps.getD i []).length).toList.take 1782).Nodup ∧
      (stageColour i (invSteps.getD i []).length).size = 1782) ∧
    (∀ i < 4, ∀ x ∈ stepPoints i, x < 1782) :=
  Certificates.certificate2301

end CFSG.Sporadic.SuzOddCore
