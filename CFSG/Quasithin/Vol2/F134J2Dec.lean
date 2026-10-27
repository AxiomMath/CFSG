module

public import CFSG.Quasithin.Vol2.F134J2Tables

public section

namespace CFSG.Quasithin.F134

@[expose] def j2DecOK (j i : ℕ) : Bool :=
  Nat.blt (j2Dec j i / 16384) 72 &&
    Nat.beq (mul14 (j2D j) (mul14 (j2Tel i) j2bC))
      (mul14 (mul14 (j2Tel (j2Dec j i / 128 % 128)) (j2D (j2Dec j i / 16384)))
        (j2Tel (j2Dec j i % 128)))

theorem j2_dec_check₀ : ∀ j < 18, ∀ i < 128, j2DecOK j i = true := by decide +kernel

theorem j2_dec_check₁ : ∀ j < 18, ∀ i < 128, j2DecOK (j + 18) i = true := by decide +kernel

theorem j2_dec_check₂ : ∀ j < 18, ∀ i < 128, j2DecOK (j + 36) i = true := by decide +kernel

theorem j2_dec_check₃ : ∀ j < 18, ∀ i < 128, j2DecOK (j + 54) i = true := by decide +kernel

theorem j2_dec_check : ∀ j < 72, ∀ i < 128, j2DecOK j i = true := by
  intro j hj
  rcases Nat.lt_or_ge j 18 with h | h
  · exact j2_dec_check₀ j h
  rcases Nat.lt_or_ge j 36 with h' | h'
  · have := j2_dec_check₁ (j - 18) (by omega)
    rwa [Nat.sub_add_cancel h] at this
  rcases Nat.lt_or_ge j 54 with h'' | h''
  · have := j2_dec_check₂ (j - 36) (by omega)
    rwa [Nat.sub_add_cancel h'] at this
  · have := j2_dec_check₃ (j - 54) (by omega)
    rwa [Nat.sub_add_cancel h''] at this

theorem j2_dec_spec {j i : ℕ} (hj : j < 72) (hi : i < 128) : j2Dec j i / 16384 < 72 ∧
    mul14 (j2D j) (mul14 (j2Tel i) j2bC) =
      mul14 (mul14 (j2Tel (j2Dec j i / 128 % 128)) (j2D (j2Dec j i / 16384)))
        (j2Tel (j2Dec j i % 128)) := by
  have h := j2_dec_check j hj i hi
  simp only [j2DecOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact h

end CFSG.Quasithin.F134
