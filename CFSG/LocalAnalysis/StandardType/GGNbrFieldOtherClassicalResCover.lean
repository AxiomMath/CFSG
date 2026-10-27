module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCover

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGFieldClassicalResidualTwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ lab.rank = 2 ∧ p = 3 ∧ lab.n = 6) ∨
    (lab.tag = .twA ∧ lab.rank = 2 ∧ p = 3 ∧ lab.n = 3)

theorem ggFieldOtherC9Label_dvd_n_of_A {p : ℕ} {lab : LargeEvenLabel}
    (hc : GGFieldOtherC9Label p lab) (ht : lab.tag = .A) : p ∣ lab.n := by
  by_contra h
  exact hc.1.1.1.1.2.1 ⟨Or.inr (Or.inl ⟨Or.inl ht, h⟩), fun h' => by rw [ht] at h'; cases h'.1⟩

theorem ggFieldOtherC9Label_dvd_n_of_twA {p : ℕ} (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hc : GGFieldOtherC9Label p lab) (ht : lab.tag = .twA) : p ∣ lab.n := by
  by_contra h
  exact hc.1.1.1.1.2.1 ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp2, Or.inr (Or.inr
    ⟨Or.inl ht, h⟩)⟩)))), fun h' => by rw [ht] at h'; cases h'.1⟩

theorem ggFieldClassicalResidual_split {p : ℕ} (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hc : GGFieldOtherC9Label p lab) (hr : GGFieldClassicalResidualLabel p lab) :
    (lab.tag = .A ∧ lab.rank = 2 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1 ∧ 3 ∣ lab.n ∧ lab.n ≠ 6) ∨
      (lab.tag = .twA ∧ lab.rank = 2 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1 ∧ 3 ∣ lab.n ∧ lab.n ≠ 3) ∨
      (lab.tag = .twA ∧ lab.rank = 4 ∧ p = 5 ∧ 5 ∣ 2 ^ lab.n + 1 ∧ 5 ∣ lab.n) ∨
      ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2 ∧ p = 3 ∧ lab.n = 3) ∨
      GGFieldClassicalResidualTwoLabel p lab := by
  rcases hr with ⟨ht, hl, hp, hq⟩ | ⟨ht, hl, hp, hq⟩ | ⟨ht, hl, hp, hq⟩ | h
  · have hd : 3 ∣ lab.n := hp ▸ ggFieldOtherC9Label_dvd_n_of_A hc ht
    by_cases h6 : lab.n = 6
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, hl, hp, h6⟩))))
    · exact Or.inl ⟨ht, hl, hp, hq, hd, h6⟩
  · have hd : 3 ∣ lab.n := hp ▸ ggFieldOtherC9Label_dvd_n_of_twA hp2 hc ht
    by_cases h3 : lab.n = 3
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, hl, hp, h3⟩))))
    · exact Or.inr (Or.inl ⟨ht, hl, hp, hq, hd, h3⟩)
  · have hd : 5 ∣ lab.n := hp ▸ ggFieldOtherC9Label_dvd_n_of_twA hp2 hc ht
    exact Or.inr (Or.inr (Or.inl ⟨ht, hl, hp, hq, hd⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

end CFSG.StandardType

end
