module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open CFSG.Blueprint (LieModel)

@[expose] def K_LieModelNotL2 : Prop :=
  ∀ (X : Type) [Group X] (t : CFSG.Open.StatedLieTag) (n r f q' : ℕ),
    r ≠ 2 → (t ≠ .PSL ∨ n ≠ 2) → CFSG.Open.StatedLieAdmissible t n r f →
      LieModel X t n r f → IsL2Over17 X q' → False

theorem isL2Over17_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {q : ℕ}
    (h : IsL2Over17 Y q) : IsL2Over17 X q := by
  obtain ⟨r, f, hr, hr2, hq, hf, hm⟩ := h
  exact ⟨r, f, hr, hr2, hq, hf, hm.of_mulEquiv e.symm⟩

theorem not_isL2Over17_three (X : Type) [Group X] : ¬ IsL2Over17 X 3 := by
  rintro ⟨r, f, hr, hr2, hq, hf, hm⟩
  have hr3 : r = 3 := by
    have hdvd : r ∣ 3 := by
      rw [hq]
      exact dvd_pow_self r (by omega)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact absurd h hr.one_lt.ne'
    · exact h
  subst hr3
  have hf1 : f = 1 := by
    by_contra hf'
    have h2 : 2 ≤ f := by omega
    have hpow : 3 ^ 2 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) h2
    rw [← hq] at hpow
    norm_num at hpow
  subst hf1
  have hadm := hm.admissible
  simp [CFSG.Open.StatedLieAdmissible] at hadm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
