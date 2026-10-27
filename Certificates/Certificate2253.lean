
module

public import Certificates.Certificate2253Base

public import CFSG.Sporadic.Schreier.RuArrays
import Certificates.Kernel.SporSch.Ru.C2253P

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate2253 : (eqA 4060 (ruField4060 1)[0]! ruC0A = true ∧ eqA 4060 (ruField4060 1)[1]! ruC1A = true ∧
      eqA 4060 (ruField4060 2)[0]! ruNs0A = true ∧ eqA 4060 (ruField4060 2)[1]! ruNs1A = true ∧
      eqA 4060 (ruField4060 3)[0]! ruC0A = true ∧ eqA 4060 (ruField4060 3)[1]! ruC1A = true ∧
      eqA 4060 (ruField4060 3)[2]! ruNs0A = true ∧ eqA 4060 (ruField4060 3)[3]! ruNs1A = true ∧
      eqA 1920 (ruField1920 0)[0]! (resA ruF ruFPos ruC0A) = true ∧
      eqA 1920 (ruField1920 0)[1]! (resA ruF ruFPos ruC1A) = true ∧
      (∀ i < 4, eqA 1920 (ruField1920 1)[i]! (resA ruF ruFPos ruSGensA[i]!) = true) ∧
      (∀ i < 8, eqA 1920 (ruField1920 2)[i]! (resA ruF ruFPos ruKGensA[i]!) = true) ∧
      (∀ i < 6, eqA 1920 (ruField1920 3)[i]! (resA ruF ruFPos ruJGensA[i]!) = true) ∧
      (∀ i < 5, eqA 1920 (ruField1920 4)[i]! (resA ruF ruFPos ruRGensA[i]!) = true) ∧
      eqA 80 ruField80[0]! (resA ruY ruYPos ruC0A) = true ∧
      eqA 80 ruField80[1]! (resA ruY ruYPos ruC1A) = true
    )
    ∧ (eqA 4060 ruZA (idA 4060) = false ∧ eqA 4060 (compA 4060 ruZA ruZA) (idA 4060) = true ∧
      eqA 4060 (compA 4060 ruZA ruC0A) (compA 4060 ruC0A ruZA) = true ∧
      eqA 4060 (compA 4060 ruZA ruC1A) (compA 4060 ruC1A ruZA) = true ∧
      (∀ i < 80, ruZA[ruY[i]!]! = ruY[i]!)
    )
    ∧ ((∀ i < 6, ∀ g < 2, imgSorted #[ruC0A, ruC1A][g]! (ruCBlockList i) =
        ruCBlockList (ruCBlockPerms.getD g #[])[i]!) ∧
      (∀ i < 7, ∀ g < 2, imgSorted #[ruNs0A, ruNs1A][g]! (ruNBlockList i) =
        ruNBlockList (ruNBlockPerms.getD g #[])[i]!) ∧
      (∀ i < 6, ∀ j < 6, imgSorted ruJGensA[j]! (ruCBlockList i) = ruCBlockList i) ∧
      (∀ i < 7, ∀ j < 8, imgSorted ruKGensA[j]! (ruNBlockList i) = ruNBlockList i) ∧
      (∀ i < 6, (ruCBlockList i).Pairwise (· < ·) ∧ ∀ x ∈ ruCBlockList i, x < 4060) ∧
      (∀ i < 7, (ruNBlockList i).Pairwise (· < ·) ∧ ∀ x ∈ ruNBlockList i, x < 4060) ∧
      ((List.range 6).map ruCBlockList).Nodup ∧ ((List.range 7).map ruNBlockList).Nodup ∧
      (∀ g < 2, ∀ i < 6, (ruCBlockPerms.getD g #[])[i]! < 6) ∧
      (∀ g < 2, ∀ i < 7, (ruNBlockPerms.getD g #[])[i]! < 7) ∧
      ruCBlockStrong[0]! = ruCBlockPerms.getD 0 #[] ∧ ruCBlockStrong[1]! = ruCBlockPerms.getD 1 #[] ∧
      ruNBlockStrong[0]! = ruNBlockPerms.getD 0 #[] ∧
      ruNBlockStrong[1]! = ruNBlockPerms.getD 1 #[]
    ) := KernelSporSch.RuCe.facts

end Certificates
