module

public import Certificates.Kernel.Co2X9.BlkA
public import Certificates.Kernel.Co2X9.BlkB

public section

namespace CertificateChecks.KernelSpor.Co2X9

open CFSG.KC.Co2X9

theorem blks : ∀ b < 96, blkX EN.CF GX DX WK 6144 b = true := by
  intro b hb
  by_cases h : b < 48
  · have e : Nat.add 0 b = b := Nat.zero_add b
    rw [← e]
    exact blkA b h
  · have e : Nat.add 48 (b - 48) = b := Nat.add_sub_of_le (by omega)
    rw [← e]
    exact blkB (b - 48) (by omega)

end CertificateChecks.KernelSpor.Co2X9

end
