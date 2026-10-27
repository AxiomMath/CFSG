module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_16R (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M,
    (¬ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsChev (BarInf L) p) →
      (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ (∃ n : ℕ, IsSU3 (Bar2 L) n) ∨
      (∃ n : ℕ, IsL2 (Bar2 L) n) ∨ (∃ n : ℕ, IsSz (Bar2 L) n) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsL2Odd (Bar2 L) p) ∨ IsJ1 (Bar2 L)

theorem s21_16R_of_s21_16 {D : Data G} {Ch : Choice2011 G} (h : S21_16 D Ch) : S21_16R D Ch :=
  fun h1930 c L hL _ => h h1930 c L hL

theorem s21_16_of_s21_16R {D : Data G} {Ch : Choice2011 G} (h212 : S21_12 D Ch)
    (h : S21_16R D Ch) : S21_16 D Ch := by
  intro h1930 c L hL
  by_cases hch : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsChev (BarInf L) p
  · obtain ⟨p, hp, hp2, hC⟩ := hch
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, hp2, (h212 h1930 c L hL p hp hp2 hC).1⟩))))
  · exact h h1930 c L hL hch

end CFSG.LocalAnalysis.UniquenessCase.UC22
