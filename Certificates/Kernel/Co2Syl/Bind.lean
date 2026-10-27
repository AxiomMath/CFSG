module

public import Certificates.Kernel.Co2Syl.D1
public import Certificates.Kernel.Co2Syl.D3
public import Certificates.Kernel.Co2Syl.D4
public import Certificates.Kernel.Co2Syl.D5
public import Certificates.Kernel.Co2Syl.D6
public import Certificates.Kernel.Co2Syl.D8
public import CFSG.RankThree.Co2.XData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Syl

open CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.RankThree.Co2

theorem gens1 : ∀ j < 5, Nat.beq (G1 j) (wordK pWords1[j]!) = true := by kc_cover 5
theorem gens3 : ∀ j < 5, Nat.beq (G3 j) (wordK pWords3[j]!) = true := by kc_cover 5
theorem gens4 : ∀ j < 4, Nat.beq (G4 j) (wordK pWords4[j]!) = true := by kc_cover 4
theorem gens4pad : Nat.beq (G4 4) (G4 3) = true := by quickRfl
theorem gens5 : ∀ j < 5, Nat.beq (G5 j) (wordK pWords5[j]!) = true := by kc_cover 5
theorem gens6 : ∀ j < 5, Nat.beq (G6 j) (wordK pWords6[j]!) = true := by kc_cover 5
theorem gens8 : ∀ j < 5, Nat.beq (G8 j) (wordK pWords8[j]!) = true := by kc_cover 5

theorem reps : ∀ i < 10, Nat.beq (RP i) (wordK RW[i]!) = true := by kc_cover 10

theorem ut1 : utK B1 Bi1 G1 = true := by quickRfl
theorem ut3 : utK B3 Bi3 G3 = true := by quickRfl
theorem ut4 : utK B4 Bi4 G4 = true := by quickRfl
theorem ut5 : utK B5 Bi5 G5 = true := by quickRfl
theorem ut6 : utK B6 Bi6 G6 = true := by quickRfl
theorem ut8 : utK B8 Bi8 G8 = true := by quickRfl

theorem zero1 : Nat.beq (elemAt E1.CF 0) IDP = true := by quickRfl
theorem zero3 : Nat.beq (elemAt E3.CF 0) IDP = true := by quickRfl
theorem zero4 : Nat.beq (elemAt E4.CF 0) IDP = true := by quickRfl
theorem zero5 : Nat.beq (elemAt E5.CF 0) IDP = true := by quickRfl
theorem zero6 : Nat.beq (elemAt E6.CF 0) IDP = true := by quickRfl
theorem zero8 : Nat.beq (elemAt E8.CF 0) IDP = true := by quickRfl

theorem one1 : Nat.beq (mOf (recAt E1.CF 0)) 1 = true := by quickRfl
theorem one3 : Nat.beq (mOf (recAt E3.CF 0)) 1 = true := by quickRfl
theorem one4 : Nat.beq (mOf (recAt E4.CF 0)) 1 = true := by quickRfl
theorem one5 : Nat.beq (mOf (recAt E5.CF 0)) 1 = true := by quickRfl
theorem one6 : Nat.beq (mOf (recAt E6.CF 0)) 1 = true := by quickRfl
theorem one8 : Nat.beq (mOf (recAt E8.CF 0)) 1 = true := by quickRfl

theorem mem1 : memK E1.CF 131072 (RP 1) (lAt MI1 0) = true := by quickRfl
theorem mem3a : memK E3.CF 65536 (RP 2) (lAt MI3 0) = true := by quickRfl
theorem mem3b : memK E3.CF 65536 (RP 3) (lAt MI3 1) = true := by quickRfl
theorem mem4 : memK E4.CF 32768 (RP 4) (lAt MI4 0) = true := by quickRfl
theorem mem5a : memK E5.CF 16384 (RP 5) (lAt MI5 0) = true := by quickRfl
theorem mem5b : memK E5.CF 16384 (RP 6) (lAt MI5 1) = true := by quickRfl
theorem mem6a : memK E6.CF 16384 (RP 5) (lAt MI6 0) = true := by quickRfl
theorem mem6b : memK E6.CF 16384 (RP 6) (lAt MI6 1) = true := by quickRfl
theorem mem8a : memK E8.CF 16384 (RP 7) (lAt MI8 0) = true := by quickRfl
theorem mem8b : memK E8.CF 16384 (RP 8) (lAt MI8 1) = true := by quickRfl

theorem comm1 : ∀ j < 5, commK (G1 j) (RP 1) = true := by kc_cover 5
theorem comm3a : ∀ j < 5, commK (G3 j) (RP 2) = true := by kc_cover 5
theorem comm3b : ∀ j < 5, commK (G3 j) (RP 3) = true := by kc_cover 5
theorem comm4 : ∀ j < 5, commK (G4 j) (RP 4) = true := by kc_cover 5
theorem comm5a : ∀ j < 5, commK (G5 j) (RP 5) = true := by kc_cover 5
theorem comm5b : ∀ j < 5, commK (G5 j) (RP 6) = true := by kc_cover 5
theorem comm6a : ∀ j < 5, commK (G6 j) (RP 5) = true := by kc_cover 5
theorem comm6b : ∀ j < 5, commK (G6 j) (RP 6) = true := by kc_cover 5
theorem comm8a : ∀ j < 5, commK (G8 j) (RP 7) = true := by kc_cover 5
theorem comm8b : ∀ j < 5, commK (G8 j) (RP 8) = true := by kc_cover 5

theorem wit6 : witK E6.CF (RP 0) 16384 WA6 WB6 = true := by quickRfl
theorem wit8 : witK E8.CF (RP 0) 16384 WA8 WB8 = true := by quickRfl

theorem cnt1A : Nat.beq (cntTotal CNT1 0 32) 2304 = true := by quickRfl
theorem cnt1B : Nat.beq (cntTotal CNT1 1 32) 768 = true := by quickRfl
theorem cnt3A : Nat.beq (cntTotal CNT3 0 16) 1152 = true := by quickRfl
theorem cnt3B : Nat.beq (cntTotal CNT3 1 16) 384 = true := by quickRfl
theorem cnt4A : Nat.beq (cntTotal CNT4 0 8) 128 = true := by quickRfl
theorem cnt4B : Nat.beq (cntTotal CNT4 1 8) 192 = true := by quickRfl
theorem cnt5A : Nat.beq (cntTotal CNT5 0 4) 256 = true := by quickRfl
theorem cnt5B : Nat.beq (cntTotal CNT5 1 4) 0 = true := by quickRfl

end CertificateChecks.KernelSpor.Co2Syl

end
