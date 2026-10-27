module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcDefs

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H] {s : ℕ} {Hs : ℕ → Subgroup H}

theorem le_five_of_two_cores (h6 : 6 ≤ s) (h7 : s ≠ 7)
    (habel : ∀ k : ℕ, k < s → 3 * k ≤ 2 * s → Abel Hs k)
    (hcore : ∀ i₁ i₂ : ℕ, 1 ≤ i₁ → i₁ < i₂ → 2 * i₂ ≤ s → Abel Hs (s - i₁) → False) : False :=
  hcore ((s + 2) / 3) ((s + 2) / 3 + 1) (by omega) (by omega) (by omega)
    (habel (s - (s + 2) / 3) (by omega) (by omega))

end CFSG.Quasithin.Fan86.Tutte
