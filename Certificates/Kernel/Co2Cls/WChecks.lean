module

public import Certificates.Kernel.Co2Cls.Small
public import Certificates.Kernel.Co2Cls.WWords
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Cls

open CFSG.KC.Co2InvS CertificateChecks.KernelSpor.Co2Syl

theorem word1 : ∀ j < 2, Nat.beq (lAt W1 j) (wordK (WW1.getD j [])) = true := by kc_cover 2
theorem word2 : ∀ j < 2, Nat.beq (lAt W2 j) (wordK (WW2.getD j [])) = true := by kc_cover 2
theorem word3 : ∀ j < 2, Nat.beq (lAt W3 j) (wordK (WW3.getD j [])) = true := by kc_cover 2
theorem word5 : ∀ j < 1, Nat.beq (lAt W5 j) (wordK (WW5.getD j [])) = true := by kc_cover 1
theorem word6 : ∀ j < 1, Nat.beq (lAt W6 j) (wordK (WW6.getD j [])) = true := by kc_cover 1
theorem word7 : ∀ j < 3, Nat.beq (lAt W7 j) (wordK (WW7.getD j [])) = true := by kc_cover 3
theorem word8 : ∀ j < 3, Nat.beq (lAt W8 j) (wordK (WW8.getD j [])) = true := by kc_cover 3
theorem word9 : ∀ j < 1, Nat.beq (lAt W9 j) (wordK (WW9.getD j [])) = true := by kc_cover 1

theorem words_lt :
    ∀ ws ∈ [WW1, WW2, WW3, WW5, WW6, WW7, WW8, WW9], ∀ w ∈ ws, ∀ l ∈ w, l < 42 := by
  decide +kernel

theorem pos_word : Nat.beq (lAt LT 21) (wordK [0, 21, 21]) = true := by quickRfl
theorem neg_wordJ : notK (Nat.beq (lAt W1 1) (wordK (WW1.getD 0 []))) = true := by quickRfl
theorem neg_wordT : notK (Nat.beq (lAt W1 0) (wordK (WW1.getD 0 []).tail)) = true := by quickRfl
theorem neg_wordL : notK (Nat.beq (lAt W7 2) (wordK ((WW7.getD 2 []) ++ [0]))) = true := by
  quickRfl
theorem neg_lt : ¬ ∀ w ∈ [[3, 42]], ∀ l ∈ w, l < 42 := by decide +kernel

end CertificateChecks.KernelSpor.Co2Cls

end
