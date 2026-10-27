module

public import Certificates.Kernel.Co2SmithS.Lets
public import Certificates.Data.Kernel.Co2SmithS.Rows

public section

namespace CertificateChecks.KernelCo2SmithS

open CFSG.KC.Co2SmithS CFSG.KC.Co2InvS CFSG.Sporadic.Co2Smith.Native

theorem lt_bounds : (aWord.all (· < 2) && bWord.all (· < 2) &&
    (List.range 16).all fun k => (sp6LetterMix k).all (· < 4)) = true := by decide +kernel

theorem lt_ab : (Nat.beq (wK LT aWord) (LT 2) && Nat.beq (wK LT bWord) (LT 3)) = true := by
  decide +kernel

theorem lt_sp6 : (List.range 16).all (fun k => Nat.beq (wK LT (sp6LetterMix k)) (LT (4 + k))) =
    true := by decide +kernel

theorem frame0_ok : (frameWords[0]!.all (· < 4) && !Nat.beq (wK LT frameWords[0]!) IDP) = true := by
  decide +kernel

theorem sp6_ok : sp6CheckK (fun k => LT (4 + k)) (mulV (LT 2) IDP) (mulV (LT 3) IDP) = true := by
  decide +kernel

end CertificateChecks.KernelCo2SmithS

end
