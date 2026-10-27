module

public import CFSG.Quasithin.Vol2.F134M23Tables

public section

namespace CFSG.Quasithin.F134

@[expose] def m23DecOK (c j s : ℕ) : Bool :=
  Nat.blt (m23GDecAt c (4 * j + s) / 16384) 835 &&
    Nat.beq (mul23 (mul23 (m23D j) (m23Tel ((m23GRL.getD c []).getD s 0))) (m23G c))
      (mul23 (mul23 (m23Tel (m23GDecAt c (4 * j + s) / 128 % 128))
        (m23D (m23GDecAt c (4 * j + s) / 16384))) (m23Tel (m23GDecAt c (4 * j + s) % 128)))

theorem m23_gdec_check₀ : ∀ j < 210, ∀ s < 4, m23DecOK 0 j s = true := by
  decide +kernel

theorem m23_gdec_check₁ : ∀ j < 210, ∀ s < 4, m23DecOK 0 (j + 210) s = true := by
  decide +kernel

theorem m23_gdec_check₂ : ∀ j < 210, ∀ s < 4, m23DecOK 0 (j + 420) s = true := by
  decide +kernel

theorem m23_gdec_check₃ : ∀ j < 205, ∀ s < 4, m23DecOK 0 (j + 630) s = true := by
  decide +kernel

theorem m23_gdec_check₄ : ∀ j < 210, ∀ s < 4, m23DecOK 1 j s = true := by
  decide +kernel

theorem m23_gdec_check₅ : ∀ j < 210, ∀ s < 4, m23DecOK 1 (j + 210) s = true := by
  decide +kernel

theorem m23_gdec_check₆ : ∀ j < 210, ∀ s < 4, m23DecOK 1 (j + 420) s = true := by
  decide +kernel

theorem m23_gdec_check₇ : ∀ j < 205, ∀ s < 4, m23DecOK 1 (j + 630) s = true := by
  decide +kernel

theorem m23_gdec_check : ∀ c < 2, ∀ j < 835, ∀ s < 4, m23DecOK c j s = true := by
  intro c hc j hj
  interval_cases c
  · rcases Nat.lt_or_ge j 210 with h | h
    · exact m23_gdec_check₀ j h
    rcases Nat.lt_or_ge j 420 with h' | h'
    · have := m23_gdec_check₁ (j - 210) (by omega)
      rwa [Nat.sub_add_cancel h] at this
    rcases Nat.lt_or_ge j 630 with h'' | h''
    · have := m23_gdec_check₂ (j - 420) (by omega)
      rwa [Nat.sub_add_cancel h'] at this
    · have := m23_gdec_check₃ (j - 630) (by omega)
      rwa [Nat.sub_add_cancel h''] at this
  · rcases Nat.lt_or_ge j 210 with h | h
    · exact m23_gdec_check₄ j h
    rcases Nat.lt_or_ge j 420 with h' | h'
    · have := m23_gdec_check₅ (j - 210) (by omega)
      rwa [Nat.sub_add_cancel h] at this
    rcases Nat.lt_or_ge j 630 with h'' | h''
    · have := m23_gdec_check₆ (j - 420) (by omega)
      rwa [Nat.sub_add_cancel h'] at this
    · have := m23_gdec_check₇ (j - 630) (by omega)
      rwa [Nat.sub_add_cancel h''] at this

theorem m23_gdec_spec {c j s : ℕ} (hc : c < 2) (hj : j < 835) (hs : s < 4) :
    m23GDecAt c (4 * j + s) / 16384 < 835 ∧
    mul23 (mul23 (m23D j) (m23Tel ((m23GRL.getD c []).getD s 0))) (m23G c) =
      mul23 (mul23 (m23Tel (m23GDecAt c (4 * j + s) / 128 % 128))
        (m23D (m23GDecAt c (4 * j + s) / 16384))) (m23Tel (m23GDecAt c (4 * j + s) % 128)) := by
  have h := m23_gdec_check c hc j hj s hs
  simp only [m23DecOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact h

end CFSG.Quasithin.F134
