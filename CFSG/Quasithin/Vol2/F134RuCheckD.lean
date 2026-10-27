module

public import CFSG.Quasithin.Vol2.F134RuTables

public section

namespace CFSG.Quasithin.F134

@[expose] def ruDOK (j : ℕ) : Bool :=
  (ruDW.getD j []).all (fun l => Nat.blt l 16386) && Nat.beq (ruLWordC (ruDW.getD j [])) (ruD j)

theorem ru_d_ok₀ : ∀ j < 170, ruDOK j = true := by
  decide +kernel

theorem ru_d_ok₁ : ∀ j < 170, ruDOK (j + 170) = true := by
  decide +kernel

theorem ru_d_ok₂ : ∀ j < 170, ruDOK (j + 340) = true := by
  decide +kernel

theorem ru_d_ok₃ : ∀ j < 170, ruDOK (j + 510) = true := by
  decide +kernel

theorem ru_d_ok₄ : ∀ j < 167, ruDOK (j + 680) = true := by
  decide +kernel

theorem ru_d_ok : ∀ j < 847, ruDOK j = true := by
  intro j hj
  rcases Nat.lt_or_ge j 170 with h0 | h0
  · exact ru_d_ok₀ j h0
  rcases Nat.lt_or_ge j 340 with h1 | h1
  · have := ru_d_ok₁ (j - 170) (by omega)
    rwa [Nat.sub_add_cancel h0] at this
  rcases Nat.lt_or_ge j 510 with h2 | h2
  · have := ru_d_ok₂ (j - 340) (by omega)
    rwa [Nat.sub_add_cancel h1] at this
  rcases Nat.lt_or_ge j 680 with h3 | h3
  · have := ru_d_ok₃ (j - 510) (by omega)
    rwa [Nat.sub_add_cancel h2] at this
  · have := ru_d_ok₄ (j - 680) (by omega)
    rwa [Nat.sub_add_cancel h3] at this

theorem ru_d_check {j : ℕ} (hj : j < 847) : (∀ l ∈ ruDW.getD j [], l < 16386) ∧
    ruLWordC (ruDW.getD j []) = ruD j := by
  have h := ru_d_ok j hj
  simp only [ruDOK, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact h

end CFSG.Quasithin.F134
