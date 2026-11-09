module

public import Certificates.Data.Kernel.D42K

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD42

open CFSG.KC.D42K

theorem checkK : d42CheckK = true := by decide +kernel

theorem slp0 : ((List.range' 0 3).all d42SlpK) = true := by decide +kernel

theorem slpK3 : d42SlpK 3 = true := by decide +kernel
theorem slpK4 : d42SlpK 4 = true := by decide +kernel
theorem slpK5 : d42SlpK 5 = true := by decide +kernel
theorem slpK6 : d42SlpK 6 = true := by decide +kernel
theorem slpK7 : d42SlpK 7 = true := by decide +kernel
theorem slpK8 : d42SlpK 8 = true := by decide +kernel
theorem slpK9 : d42SlpK 9 = true := by decide +kernel
theorem slpK10 : d42SlpK 10 = true := by decide +kernel
theorem slpK11 : d42SlpK 11 = true := by decide +kernel
theorem slpK12 : d42SlpK 12 = true := by decide +kernel
theorem slpK13 : d42SlpK 13 = true := by decide +kernel
theorem slpK14 : d42SlpK 14 = true := by decide +kernel
theorem slpK15 : d42SlpK 15 = true := by decide +kernel
theorem slpK16 : d42SlpK 16 = true := by decide +kernel
theorem slpK17 : d42SlpK 17 = true := by decide +kernel

theorem slp1 : ((List.range' 3 3).all d42SlpK) = true := by
  have e : List.range' 3 3 = [3, 4, 5] := rfl
  rw [e]
  simp only [List.all_cons, List.all_nil, slpK3, slpK4, slpK5, Bool.and_true]

theorem slp2 : ((List.range' 6 3).all d42SlpK) = true := by
  have e : List.range' 6 3 = [6, 7, 8] := rfl
  rw [e]
  simp only [List.all_cons, List.all_nil, slpK6, slpK7, slpK8, Bool.and_true]

theorem slp3 : ((List.range' 9 3).all d42SlpK) = true := by
  have e : List.range' 9 3 = [9, 10, 11] := rfl
  rw [e]
  simp only [List.all_cons, List.all_nil, slpK9, slpK10, slpK11, Bool.and_true]

theorem slp4 : ((List.range' 12 3).all d42SlpK) = true := by
  have e : List.range' 12 3 = [12, 13, 14] := rfl
  rw [e]
  simp only [List.all_cons, List.all_nil, slpK12, slpK13, slpK14, Bool.and_true]

theorem slp5 : ((List.range' 15 3).all d42SlpK) = true := by
  have e : List.range' 15 3 = [15, 16, 17] := rfl
  rw [e]
  simp only [List.all_cons, List.all_nil, slpK15, slpK16, slpK17, Bool.and_true]

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
