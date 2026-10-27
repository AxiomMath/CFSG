module

public import CFSG.Quasithin.Vol2.F134M24Tables

public section

namespace CFSG.Quasithin.F134

@[expose] def m24DecOK (c j s : ℕ) : Bool :=
  Nat.blt (m24GDecAt c (2 * j + s) / 1048576) 510 &&
    Nat.beq (mul24 (mul24 (m24D j) (m24Tel ((m24GRL.getD c []).getD s 0))) (m24G c))
      (mul24 (mul24 (m24Tel (m24GDecAt c (2 * j + s) / 1024 % 1024))
        (m24D (m24GDecAt c (2 * j + s) / 1048576))) (m24Tel (m24GDecAt c (2 * j + s) % 1024)))

theorem m24_gdec_check₀ : ∀ j < 255, ∀ s < 2, m24DecOK 0 j s = true := by
  decide +kernel

theorem m24_gdec_check₁ : ∀ j < 255, ∀ s < 2, m24DecOK 0 (j + 255) s = true := by
  decide +kernel

theorem m24_gdec_check₂ : ∀ j < 255, ∀ s < 2, m24DecOK 1 j s = true := by
  decide +kernel

theorem m24_gdec_check₃ : ∀ j < 255, ∀ s < 2, m24DecOK 1 (j + 255) s = true := by
  decide +kernel

theorem m24_gdec_check₄ : ∀ j < 255, ∀ s < 2, m24DecOK 2 j s = true := by
  decide +kernel

theorem m24_gdec_check₅ : ∀ j < 255, ∀ s < 2, m24DecOK 2 (j + 255) s = true := by
  decide +kernel

theorem m24_gdec_check : ∀ c < 3, ∀ j < 510, ∀ s < 2, m24DecOK c j s = true := by
  intro c hc j hj
  interval_cases c
  · rcases Nat.lt_or_ge j 255 with h | h
    · exact m24_gdec_check₀ j h
    · have := m24_gdec_check₁ (j - 255) (by omega)
      rwa [Nat.sub_add_cancel h] at this
  · rcases Nat.lt_or_ge j 255 with h | h
    · exact m24_gdec_check₂ j h
    · have := m24_gdec_check₃ (j - 255) (by omega)
      rwa [Nat.sub_add_cancel h] at this
  · rcases Nat.lt_or_ge j 255 with h | h
    · exact m24_gdec_check₄ j h
    · have := m24_gdec_check₅ (j - 255) (by omega)
      rwa [Nat.sub_add_cancel h] at this

theorem m24_gdec_spec {c j s : ℕ} (hc : c < 3) (hj : j < 510) (hs : s < 2) :
    m24GDecAt c (2 * j + s) / 1048576 < 510 ∧
    mul24 (mul24 (m24D j) (m24Tel ((m24GRL.getD c []).getD s 0))) (m24G c) =
      mul24 (mul24 (m24Tel (m24GDecAt c (2 * j + s) / 1024 % 1024))
        (m24D (m24GDecAt c (2 * j + s) / 1048576))) (m24Tel (m24GDecAt c (2 * j + s) % 1024)) := by
  have h := m24_gdec_check c hc j hj s hs
  simp only [m24DecOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact h

end CFSG.Quasithin.F134
