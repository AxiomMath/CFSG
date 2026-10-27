module

public import Certificates.Kernel.Co2J.SetsA
public import Certificates.Kernel.Co2J.SetsB

public section

namespace CertificateChecks.KernelSpor.Co2J

open CFSG.KC.Co2J

theorem sets : ∀ i < 716, setK PE SM EL INV CM RC EX MR 716 71 i = true := by
  intro i hi
  by_cases h : i < 358
  · have e : Nat.add 0 i = i := Nat.zero_add i
    rw [← e]
    exact setsA i h
  · have e : Nat.add 358 (i - 358) = i := Nat.add_sub_cancel' (by omega)
    rw [← e]
    exact setsB (i - 358) (by omega)

end CertificateChecks.KernelSpor.Co2J

end
