module

public import CFSG.GH74.GLS.Stage4.Q9.ModelBase
public import CFSG.GH74.GLS.Stage4.Q9.DFactsInputs
import CFSG.Certificates.Kernel.Q9SL2Sound
import Certificates.Kernel.Q9SL2.ChecksA
import Certificates.Kernel.Q9SL2.ChecksQ8
import Certificates.Kernel.Q9SL2.ChecksConj
import Certificates.Kernel.Q9SL2.ChecksCent

public section

open CFSG.KC.Q9SL2

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.Stage4 in
open CFSG.GH74.GLS.Stage4.Q9 in
open CFSG.GH74.GLS.Stage4.Q9.DFacts in
theorem certificate5099 : (chkSqOne = true)
    ∧ (chkCenter = true)
    ∧ (chkQ8 = true)
    ∧ (chkConjFixed5 = true)
    ∧ (chkCent5 = true)
    ∧ (chkCent3 = true)
    ∧ (chkCentOdd5 = true)
    ∧ (chkCentOdd3 = true)
    ∧ (chkSigmaNotConj = true)
    ∧ (chkInvert3 = true)
    ∧ (chkNo16 = true)
    ∧ (chkQ16 = true)
    ∧ (chkQ16card = true) :=
  ⟨chkSqOne_eq.trans chkSqOneK_true, chkCenter_eq.trans chkCenterK_true,
    chkQ8_eq.trans chkQ8K_true, chkConjFixed5_eq.trans chkConjFixed5K_true,
    chkCent5_eq.trans chkCent5K_true, chkCent3_eq.trans chkCent3K_true,
    chkCentOdd5_eq.trans chkCentOdd5K_true, chkCentOdd3_eq.trans chkCentOdd3K_true,
    chkSigmaNotConj_eq.trans chkSigmaNotConjK_true, chkInvert3_eq.trans chkInvert3K_true,
    chkNo16_eq.trans chkNo16K_true, chkQ16_eq.trans chkQ16K_true,
    chkQ16card_eq.trans chkQ16cardK_true⟩

end Certificates
