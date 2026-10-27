module

public import Certificates.Kernel.Co2Cls.DS
public import Certificates.Kernel.Co2Cls.D4
public import Certificates.Kernel.Co2Cls.D5
public import Certificates.Kernel.Co2Cls.D6
public import Certificates.Kernel.Co2Cls.D9
public import CFSG.RankThree.Co2.CensusData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Cls

open CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2Cls CertificateChecks.KernelSpor.Co2Syl
  CFSG.RankThree.Co2

theorem inv : ∀ j < 21, Nat.beq (mulV (lAt LT j) (GC j)) IDP = true := by kc_cover 21
theorem cent0 : ∀ j < 21, commK (GC j) (RP 0) = true := by kc_cover 21
theorem gensT : ∀ l < 5, Nat.beq (HT l) (wordK sylWords[l]!) = true := by kc_cover 5

theorem orb1 : ∀ a < 2, orbK (lAt O1) (lAt IX1) HT 5 2 a = true := by kc_cover 2
theorem orb2 : ∀ a < 4, orbK (lAt O2) (lAt IX2) HT 5 4 a = true := by kc_cover 4
theorem orb3 : ∀ a < 4, orbK (lAt O3) (lAt IX3) HT 5 4 a = true := by kc_cover 4
theorem orb4 : ∀ a < 8, orbK (lAt O4) (lAt IX4) HT 5 8 a = true := by kc_cover 8
theorem orb5 : ∀ a < 16, orbK (lAt O5) (lAt IX5) HT 5 16 a = true := by kc_cover 16
theorem orb6 : ∀ a < 16, orbK (lAt O6) (lAt IX6) HT 5 16 a = true := by kc_cover 16
theorem orb7 : ∀ a < 16, orbK (lAt O7) (lAt IX7) HT 5 16 a = true := by kc_cover 16
theorem orb8 : ∀ a < 16, orbK (lAt O8) (lAt IX8) HT 5 16 a = true := by kc_cover 16
theorem orb9 : ∀ a < 128, orbK (lAt O9) (lAt IX9) HT 5 128 a = true := by kc_cover 16

theorem at1 : memK C1 270 (lAt O1 0) K1 = true := by quickRfl
theorem at2 : memK C2 1260 (lAt O2 0) K2 = true := by quickRfl
theorem at3 : memK C3 1260 (lAt O3 0) K3 = true := by quickRfl
theorem at4 : memK C4 22680 (lAt O4 0) K4 = true := by quickRfl
theorem at5 : memK C5 15120 (lAt O5 0) K5 = true := by quickRfl
theorem at6 : memK C6 15120 (lAt O6 0) K6 = true := by quickRfl
theorem at7 : memK C7 1008 (lAt O7 0) K7 = true := by quickRfl
theorem at8 : memK C8 1008 (lAt O8 0) K8 = true := by quickRfl
theorem at9 : memK C9 120960 (lAt O9 0) K9 = true := by quickRfl

theorem wit1 : andK (oddW (lAt O1 0) (lAt W1 0) 3) (oddW (lAt O1 0) (lAt W1 1) 7) = true := by
  quickRfl
theorem wit2 : pairW (lAt O2 0) (lAt W2 0) (lAt W2 1) = true := by quickRfl
theorem wit3 : pairW (lAt O3 0) (lAt W3 0) (lAt W3 1) = true := by quickRfl
theorem wit5 : oddW (lAt O5 0) (lAt W5 0) 3 = true := by quickRfl
theorem wit6 : oddW (lAt O6 0) (lAt W6 0) 3 = true := by quickRfl
theorem wit7 : andK (pairW (lAt O7 0) (lAt W7 0) (lAt W7 1)) (oddW (lAt O7 0) (lAt W7 2) 5) = true :=
  by quickRfl
theorem wit8 : andK (pairW (lAt O8 0) (lAt W8 0) (lAt W8 1)) (oddW (lAt O8 0) (lAt W8 2) 5) = true :=
  by quickRfl
theorem wit9 : oddW (lAt O9 0) (lAt W9 0) 3 = true := by quickRfl

theorem witLt : ∀ i < 10, ∀ j < 3, Nat.blt (lAt ([[], W1, W2, W3, [], W5, W6, W7, W8, W9].getD i [])
    j) (Nat.shiftLeft 1 484) = true := by
  decide +kernel

end CertificateChecks.KernelSpor.Co2Cls

end
