module

public import CFSG.Quasithin.Vol2.KGFactG2RuInputs
public meta import CFSG.Quasithin.Vol2.KGFactG2RuInputs
import Certificates.Certificate2247
import Certificates.Certificate2250
import Certificates.Kernel.SporSch.Ru.G2Ru7163

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Quasithin.H13.Ch4.G2Ru in
theorem certificate7163 :
    (∀ i < 6, ∀ j < 6, eqA 4060 (compA 4060 g2WGenA[i]! g2WGenA[j]!)
      (compA 4060 g2WGenA[j]! g2WGenA[i]!) = true) ∧
      (∀ i < 6, eqA 4060 (compA 4060 g2WGenA[i]! g2WGenA[i]!) (CFSG.Monster.B.Co2.Native.idA 4060) = true) ∧
      eqA 4060 g2WGenA[0]! ruZA = true ∧
      (∀ e < 64, ∀ k < 6, g2InW (compA 4060 g2WGenA[k]! (g2WProd e)) = true) ∧
      g2InW g2VGenA[1]! = true ∧ g2InW g2VGenA[2]! = true ∧
      (∀ i < 8, ∀ j < 8, i < j → eqA 4060 g2VArr[i]! g2VArr[j]! = false) ∧
      (∀ e < 8, ∀ k < 3, g2InV (compA 4060 g2VGenA[k]! (g2VProd e)) = true) ∧
      g2RhoCheck = true ∧
      all2 4060 ruLevS (fun s => !g2NormW s || g2NormV s) = true := KernelSporSch.G2Ru7163.c7163

end Certificates
