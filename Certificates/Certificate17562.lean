module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentA2
import Certificates.Kernel.B433Alt.FiveMain

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups CFSG.YGroups.DCE.B433 CFSG.HardMathSupport.Dickson.I271.TabBFiveCent in
theorem certificate17562 : 4154781481226426191177580544000000 ≤ Nat.card B433 →
    orderOf (psi dFive) = 5 ∧ 7 ∣ Nat.card (Subgroup.centralizer {psi dFive}) ∧
      Nat.card (Subgroup.centralizer {psi dFive}) ≤ 635065200 :=
  KernelB433.card_centralizer_dFive

end Certificates
