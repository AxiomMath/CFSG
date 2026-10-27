module

import all CFSG.Fischer.F4
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408PointsBase

public section

open CFSG.Monster.B.TwoA.Unitary

namespace CertificateChecks.Batch3125

open CFSG.Monster.B.TwoA.Unitary

theorem five_twelve_mem_0 : (5 : ℕ) ∈ o14PtOrb[0]! ∧ (12 : ℕ) ∈ o14PtOrb[1]! := by
  simp only [Array.mem_def]
  decide +kernel

theorem singGen_vals_1 : singGen 3 5 = 1 ∧ singGen 0 1 = 12 := by
  decide +kernel

end CertificateChecks.Batch3125

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Unitary in
theorem certificate3125 : ((5 : ℕ) ∈ o14PtOrb[0]! ∧ (12 : ℕ) ∈ o14PtOrb[1]!)
    ∧ (singGen 3 5 = 1 ∧ singGen 0 1 = 12) := by
  exact ⟨CertificateChecks.Batch3125.five_twelve_mem_0, CertificateChecks.Batch3125.singGen_vals_1⟩

end Certificates
