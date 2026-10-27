
module

public import Certificates.Certificate2301Base

public import CFSG.Sporadic.SuzOddCore.InvGraphCheckInputs
public meta import CFSG.Sporadic.SuzOddCore.InvArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Refine
public meta import Mathlib.Data.Fintype.Card
import Certificates.Kernel.Sporadic.OddCore.S2301Final
import Certificates.Kernel.Sporadic.OddCore.S2301Neg
import CFSG.Sporadic.SuzOddCore.ArraysCheckInputs
import CFSG.Sporadic.SuzOddCore.FamilyCheckInputs
meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
meta import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate2301 : adjOK 1782 #[b0Arr, b1Arr] invNbr invNeighbors = true ∧
    (∀ x < 1782, invNbr[vArr[x]!]! = imgSorted vArr invNbr[x]!) ∧
    (∀ x < 1782, (invNbr[x]!).length = 416) ∧
    (∀ i < 4, tArr i = invRepArr i) ∧
    (∀ i < 4, ∀ s < (invSteps.getD i []).length,
      classCount (stageColour i s) ((stepPoints i).getD s 0) ≤
        ((invSteps.getD i []).getD s []).getD 1 0) ∧
    (∀ i < 4, ((stageColour i (invSteps.getD i []).length).toList.take 1782).Nodup ∧
      (stageColour i (invSteps.getD i []).length).size = 1782) ∧
    (∀ i < 4, ∀ x ∈ stepPoints i, x < 1782) := KernelSpor.S2301.facts2301

end Certificates
