module

public import CFSG.Quasithin.Vol2.F134RuTables

public section

namespace CFSG.Quasithin.F134

@[expose] def ruBadOK (j : ℕ) : Bool :=
  Nat.blt j 3 ||
    ((Nat.beq (ruBad j % 32) 5 || Nat.beq (ruBad j % 32) 7 || Nat.beq (ruBad j % 32) 13 ||
        Nat.beq (ruBad j % 32) 29) &&
      Nat.blt (ruBad j / 1024) 16384 &&
      Nat.beq (powC28 ruOneC (ruBad j % 32)
        (powC28 ruOneC (ruBad j / 32 % 32) (mulF28 (ruD j) (ruNFC (ruBad j / 1024))))) ruOneC &&
      (powC28 ruOneC (ruBad j / 32 % 32) (mulF28 (ruD j) (ruNFC (ruBad j / 1024))) != ruOneC))

theorem ru_bad_ok₀ : ∀ j < 170, ruBadOK j = true := by
  decide +kernel

theorem ru_bad_ok₁ : ∀ j < 170, ruBadOK (j + 170) = true := by
  decide +kernel

theorem ru_bad_ok₂ : ∀ j < 170, ruBadOK (j + 340) = true := by
  decide +kernel

theorem ru_bad_ok₃ : ∀ j < 170, ruBadOK (j + 510) = true := by
  decide +kernel

theorem ru_bad_ok₄ : ∀ j < 167, ruBadOK (j + 680) = true := by
  decide +kernel

theorem ru_bad_ok : ∀ j < 847, ruBadOK j = true := by
  intro j hj
  rcases Nat.lt_or_ge j 170 with h0 | h0
  · exact ru_bad_ok₀ j h0
  rcases Nat.lt_or_ge j 340 with h1 | h1
  · have := ru_bad_ok₁ (j - 170) (by omega)
    rwa [Nat.sub_add_cancel h0] at this
  rcases Nat.lt_or_ge j 510 with h2 | h2
  · have := ru_bad_ok₂ (j - 340) (by omega)
    rwa [Nat.sub_add_cancel h1] at this
  rcases Nat.lt_or_ge j 680 with h3 | h3
  · have := ru_bad_ok₃ (j - 510) (by omega)
    rwa [Nat.sub_add_cancel h2] at this
  · have := ru_bad_ok₄ (j - 680) (by omega)
    rwa [Nat.sub_add_cancel h3] at this

theorem ru_bad_check {j : ℕ} (hj : j < 847) (hj3 : 3 ≤ j) :
    (ruBad j % 32 = 5 ∨ ruBad j % 32 = 7 ∨ ruBad j % 32 = 13 ∨ ruBad j % 32 = 29) ∧
    ruBad j / 1024 < 16384 ∧
    powC28 ruOneC (ruBad j % 32)
        (powC28 ruOneC (ruBad j / 32 % 32) (mulF28 (ruD j) (ruNFC (ruBad j / 1024)))) = ruOneC ∧
    powC28 ruOneC (ruBad j / 32 % 32) (mulF28 (ruD j) (ruNFC (ruBad j / 1024))) ≠ ruOneC := by
  have h := ru_bad_ok j hj
  simp only [ruBadOK, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, bne_iff_ne,
    ne_eq] at h
  obtain ⟨⟨⟨hp, hu⟩, hpow⟩, hne⟩ := h.resolve_left (by omega)
  refine ⟨?_, hu, hpow, hne⟩
  rcases hp with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

end CFSG.Quasithin.F134
