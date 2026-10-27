module

public import Certificates.Kernel.Co2J.Data
public import Certificates.Kernel.Co2Syl.Small
public import CFSG.RankThree.Co2.CensusData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2J

open CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2J CFSG.RankThree.Co2

theorem gensT : ∀ k < 5, Nat.beq (G k) (CertificateChecks.KernelSpor.Co2Syl.wordK sylWords[k]!) =
    true := by kc_cover 5

theorem gensJ : ∀ i < 10, Nat.beq (GJ i) (CertificateChecks.KernelSpor.Co2Syl.wordK jWords[i]!) =
    true := by kc_cover 10

theorem ut : utK BT BTi G = true := by quickRfl

theorem jGen : jGenK GJ = true := by quickRfl

theorem jEnum : jEnumK GJ JE JS = true := by quickRfl

theorem jInT : jInTK G GJ JW JL = true := by quickRfl

theorem coord : coordAllK G GJ JE MK = true := by quickRfl

theorem tree : treeIK PE PM PS PT MK = true := by quickRfl

theorem invAll : invAllK PE INV 71 = true := by quickRfl

theorem tab : ∀ q < 71, tabRowK PE INV MR CM q = true := by kc_cover 8

theorem sm0 : Nat.beq (SM 0) 1 = true := by quickRfl

end CertificateChecks.KernelSpor.Co2J

end
