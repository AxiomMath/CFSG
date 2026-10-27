module

public import CFSG.Monster.B.Fischer.PinnedChain
public meta import CFSG.Monster.B.Fischer.PinnedChain
public import CFSG.Monster.B.Fischer.PinnedBridgeChecksInputs
public import Certificates.Certificate3040

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Co2.Native

theorem bridge_check :
    isInvA 3510 pinXiRaw (invCand 3510 pinXiRaw) = true ∧
    (∀ k < 13, lettersOK 19 (pinWord k) = true ∧
      eqA 3510 (wordA 3510 fi22StrongArrs fi22StrongInvs (pinWord k))
        (compA 3510 (compA 3510 pinXiRaw (indCandidate k)) (invCand 3510 pinXiRaw)) = true) ∧
    (pinMembership.map fun m => m.strongGeneratorWord.length) =
      [14, 12, 18, 16, 20, 12, 21, 16, 16, 17, 16, 5, 8] ∧
    (pinMembership.map fun m => m.modelGenerator) = List.range 13 :=
  Certificates.certificate3040

end CFSG.Monster.B.Fischer
