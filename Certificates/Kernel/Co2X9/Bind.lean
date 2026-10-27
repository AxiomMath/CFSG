module

public import Certificates.Kernel.Co2X9.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2X9

open CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2X9 CertificateChecks.KernelSpor.Co2Syl

theorem gens : ∀ j < 4, Nat.beq (GX j) (wordK XW[j]!) = true := by kc_cover 4
theorem gensPad : Nat.beq (GX 4) (GX 3) = true := by quickRfl
theorem XW_size : XW.size = 4 := by decide +kernel
theorem XW_lt : ∀ j < 4, ∀ l ∈ XW[j]!, l < 42 := by decide +kernel

theorem dX : Nat.beq DX (wordK DW) = true := by quickRfl
theorem fX : Nat.beq FX (wordK FW) = true := by quickRfl
theorem eX : Nat.beq EX (wordK EW) = true := by quickRfl
theorem DW_lt : ∀ l ∈ DW, l < 42 := by decide +kernel
theorem FW_lt : ∀ l ∈ FW, l < 42 := by decide +kernel
theorem EW_lt : ∀ l ∈ EW, l < 42 := by decide +kernel

theorem zero : Nat.beq (elemAt EN.CF 0) IDP = true := by quickRfl
theorem one : Nat.beq (mOf (recAt EN.CF 0)) 1 = true := by quickRfl
theorem numX : Nat.beq EN.N 6144 = true := by quickRfl

theorem comm9 : ∀ j < 5, commK (GX j) (RP 9) = true := by kc_cover 5
theorem commD : ∀ j < 5, commK (GX j) DX = true := by kc_cover 5
theorem neD : neK DX = true := by quickRfl
theorem ltD : Nat.blt DX (Nat.pow 2 484) = true := by quickRfl
theorem sqD : sqWK EN.CF 6144 DX YX = true := by quickRfl
theorem conj9 : conjK FX (RP 9) (mulV (RP 9) DX) = true := by quickRfl
theorem conj1 : conjK EX (RP 1) (mulV (RP 0) DX) = true := by quickRfl

end CertificateChecks.KernelSpor.Co2X9

end
