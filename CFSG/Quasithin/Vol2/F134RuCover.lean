module

public import CFSG.Quasithin.Vol2.F134RuTables

public section

namespace CFSG.Quasithin.F134

@[expose] def ruDecOK (c j s : ℕ) : Bool :=
  Nat.blt (ruDec c (ruM c * j + s) / 268435456) 847 &&
    Nat.blt (ruR c s) 16384 &&
    Nat.beq (mulF28 (mulF28 (ruD j) (ruNFC (ruR c s))) (ruG c))
      (mulF28 (mulF28 (ruNFC (ruDec c (ruM c * j + s) / 16384 % 16384))
        (ruD (ruDec c (ruM c * j + s) / 268435456))) (ruNFC (ruDec c (ruM c * j + s) % 16384)))

@[expose] def ruDecOKr (c j : ℕ) : Bool := (List.range (ruM c)).all fun s => ruDecOK c j s

theorem ru_gdec_ok₀₀ : ∀ j < 142, ruDecOKr 0 j = true := by
  decide +kernel

theorem ru_gdec_ok₀₁ : ∀ j < 142, ruDecOKr 0 (j + 142) = true := by
  decide +kernel

theorem ru_gdec_ok₀₂ : ∀ j < 142, ruDecOKr 0 (j + 284) = true := by
  decide +kernel

theorem ru_gdec_ok₀₃ : ∀ j < 142, ruDecOKr 0 (j + 426) = true := by
  decide +kernel

theorem ru_gdec_ok₀₄ : ∀ j < 142, ruDecOKr 0 (j + 568) = true := by
  decide +kernel

theorem ru_gdec_ok₀₅ : ∀ j < 137, ruDecOKr 0 (j + 710) = true := by
  decide +kernel

theorem ru_gdec_ok₀ : ∀ j < 847, ruDecOKr 0 j = true := by
  intro j hj
  rcases Nat.lt_or_ge j 142 with h0 | h0
  · exact ru_gdec_ok₀₀ j h0
  rcases Nat.lt_or_ge j 284 with h1 | h1
  · have := ru_gdec_ok₀₁ (j - 142) (by omega)
    rwa [Nat.sub_add_cancel h0] at this
  rcases Nat.lt_or_ge j 426 with h2 | h2
  · have := ru_gdec_ok₀₂ (j - 284) (by omega)
    rwa [Nat.sub_add_cancel h1] at this
  rcases Nat.lt_or_ge j 568 with h3 | h3
  · have := ru_gdec_ok₀₃ (j - 426) (by omega)
    rwa [Nat.sub_add_cancel h2] at this
  rcases Nat.lt_or_ge j 710 with h4 | h4
  · have := ru_gdec_ok₀₄ (j - 568) (by omega)
    rwa [Nat.sub_add_cancel h3] at this
  · have := ru_gdec_ok₀₅ (j - 710) (by omega)
    rwa [Nat.sub_add_cancel h4] at this

theorem ru_gdec_ok₁₀ : ∀ j < 283, ruDecOKr 1 j = true := by
  decide +kernel

theorem ru_gdec_ok₁₁ : ∀ j < 283, ruDecOKr 1 (j + 283) = true := by
  decide +kernel

theorem ru_gdec_ok₁₂ : ∀ j < 281, ruDecOKr 1 (j + 566) = true := by
  decide +kernel

theorem ru_gdec_ok₁ : ∀ j < 847, ruDecOKr 1 j = true := by
  intro j hj
  rcases Nat.lt_or_ge j 283 with h0 | h0
  · exact ru_gdec_ok₁₀ j h0
  rcases Nat.lt_or_ge j 566 with h1 | h1
  · have := ru_gdec_ok₁₁ (j - 283) (by omega)
    rwa [Nat.sub_add_cancel h0] at this
  · have := ru_gdec_ok₁₂ (j - 566) (by omega)
    rwa [Nat.sub_add_cancel h1] at this

theorem ru_gdec_spec {c j s : ℕ} (hc : c < 2) (hj : j < 847) (hs : s < ruM c) :
    ruDec c (ruM c * j + s) / 268435456 < 847 ∧ ruR c s < 16384 ∧
    mulF28 (mulF28 (ruD j) (ruNFC (ruR c s))) (ruG c) =
      mulF28 (mulF28 (ruNFC (ruDec c (ruM c * j + s) / 16384 % 16384))
        (ruD (ruDec c (ruM c * j + s) / 268435456))) (ruNFC (ruDec c (ruM c * j + s) % 16384)) := by
  have hr : ruDecOKr c j = true := by
    interval_cases c
    · exact ru_gdec_ok₀ j hj
    · exact ru_gdec_ok₁ j hj
  simp only [ruDecOKr, List.all_eq_true, List.mem_range] at hr
  have h := hr s hs
  simp only [ruDecOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

end CFSG.Quasithin.F134
