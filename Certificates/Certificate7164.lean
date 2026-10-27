module

public import CFSG.Quasithin.Vol2.KGFactG2RuInputs
public meta import CFSG.Quasithin.Vol2.KGFactG2RuInputs
import Certificates.Kernel.SporSch.Ru.G2Ru7164

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Quasithin.H13.Ch4.G2Ru in
theorem certificate7164 :
    g2CentV g2XA = true ∧ g2NormW g2XA = false ∧
      (∀ j < 2, g2NormW (g2NA j) = true ∧ g2NormV (g2NA j) = true ∧
        g2NormW (g2CommA (g2NA j) g2XA) = true) ∧
      (∀ m < 3, g2InV (g2DA m) = true) ∧
      (∀ i < 8, ∀ j < 8, i < j → eqA 4060 (g2DProd i) (g2DProd j) = false) ∧
      (∀ i < 3, g2NormW (g2AA i) = true ∧ g2CentV (g2AA i) = true ∧
        g2CentW (compA 4060 (g2AA i) (g2AA i)) = true) ∧
      (∀ i < 3, ∀ j < 3,
        g2SameW (compA 4060 (g2AA i) (g2AA j)) (compA 4060 (g2AA j) (g2AA i)) = true) ∧
      (∀ e < 8, ∀ e' < 8, e < e' → g2SameW (g2AProd e) (g2AProd e') = false) := KernelSporSch.G2Ru7164.c7164

end Certificates
