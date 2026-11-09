module

public import Certificates.Kernel.D4.ChainBD
public import Certificates.Kernel.Sporadic.RawGenSplitP
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#ks_rawchain_sl2_lvp CertificateChecks.KernelD4.CB 1 0 7
#ks_rawchain_sl2_lvp CertificateChecks.KernelD4.CB 1 8 10

public section

namespace CertificateChecks.KernelD4.CB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem lsP1_7a : lvSlKP 2457 12 (mask 12) (2457 * 12) S SI TR TRI 9 (stepsAt 2457 12 S 9 BP 1)
    (LR 1) 1792 128 = true := by quickRfl

theorem lsP1_7b : lvSlKP 2457 12 (mask 12) (2457 * 12) S SI TR TRI 9 (stepsAt 2457 12 S 9 BP 1)
    (LR 1) 1920 128 = true := by quickRfl

theorem ls1_7 : lvSlK 2457 12 (mask 12) (2457 * 12) S SI TR TRI 9 (stepsAt 2457 12 S 9 BP 1)
    (LR 1) (7 * 256) 256 = true := by
  refine lvSlK_of_P _ _ _ _ _ _ _ _ _ _ _ (by quickRfl) ?_
  have ha := allN_spec lsP1_7a
  have hb := allN_spec lsP1_7b
  unfold lvSlKP
  refine allN_of_forall fun d hd => ?_
  by_cases h : d < 128
  · exact ha d h
  · have e : Nat.add (7 * 256) d = Nat.add 1920 (d - 128) := by
      simp only [Nat.add_eq]
      omega
    rw [e]
    exact hb (d - 128) (by omega)

end CertificateChecks.KernelD4.CB

end
