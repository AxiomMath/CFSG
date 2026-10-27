module

public import Certificates.Data.Kernel.D42K

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD42

open CFSG.KC.D42K

theorem checkK : d42CheckK = true := by decide +kernel

theorem slp0 : ((List.range' 0 3).all d42SlpK) = true := by decide +kernel
theorem slp1 : ((List.range' 3 3).all d42SlpK) = true := by decide +kernel
theorem slp2 : ((List.range' 6 3).all d42SlpK) = true := by decide +kernel
theorem slp3 : ((List.range' 9 3).all d42SlpK) = true := by decide +kernel
theorem slp4 : ((List.range' 12 3).all d42SlpK) = true := by decide +kernel
theorem slp5 : ((List.range' 15 3).all d42SlpK) = true := by decide +kernel

theorem slpAll : ∀ k < 18, d42SlpK k = true := by
  intro k hk
  have h : ∀ b, ((List.range' b 3).all d42SlpK) = true → ∀ k, b ≤ k → k < b + 3 →
      d42SlpK k = true := fun b h k h1 h2 =>
    List.all_eq_true.1 h k (List.mem_range'_1.2 ⟨h1, h2⟩)
  by_cases h0 : k < 3
  · exact h 0 slp0 k (by omega) (by omega)
  by_cases h1 : k < 6
  · exact h 3 slp1 k (by omega) (by omega)
  by_cases h2 : k < 9
  · exact h 6 slp2 k (by omega) (by omega)
  by_cases h3 : k < 12
  · exact h 9 slp3 k (by omega) (by omega)
  by_cases h4 : k < 15
  · exact h 12 slp4 k (by omega) (by omega)
  · exact h 15 slp5 k (by omega) (by omega)

end CertificateChecks.KernelD42

end
