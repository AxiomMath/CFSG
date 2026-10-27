module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.CoverData
import Certificates.Kernel.HS3850.CoverFacts

public section

namespace Certificates

open CFSG.EvenSporadicStandard.TwoHS CFSG.EvenSporadicStandard.HSStd in
theorem certificate25552 :
    (coverNInvOK = true ∧ coverXNeOK = true ∧ coverXSqOK = true ∧ coverComm2OK = true ∧
      coverComm3OK = true ∧ coverConj3OK = true) ∧
    (coverMemOK (foursTbl 0) = true ∧ coverMemOK (coverConjTbl 0) = true ∧
      coverPermOK rho2 = true ∧ coverConjEqOK (foursTbl 0) (coverConjTbl 0) rho2 = true) ∧
    (coverMemOK (foursTbl 1) = true ∧ coverMemOK (coverConjTbl 1) = true ∧
      coverPermOK rho3 = true ∧ coverConjEqOK (foursTbl 1) (coverConjTbl 1) rho3 = true) := CFSG.KD.HS3850.facts25552

end Certificates
