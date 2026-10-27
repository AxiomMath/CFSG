module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xa

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_21B (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, c.B ≠ ⊥ → Hyp2120 D c → ∀ p ∈ D.sig,
    Hinf D.M = Opp p (oTwoEOf D.M) ∧ CFSG.Open.evenRank G = 3 ∧
    ∃ n : ℕ,
      ((IsL2Square (Bar2 (Opp p (oTwoEOf D.M))) n ∧
          CFSG.Open.pRank p (Opp p (barPreimage D.M (centE D.M))) = 1) ∨
        ((∃ (A B : Type) (_ : Group A) (_ : Group B),
            Nonempty (Bar2 (Opp p (oTwoEOf D.M)) ≃* A × B) ∧ IsU3 A n ∧ IsL2 B n) ∧
          Opp p (barPreimage D.M (centE D.M)) = ⊥)) ∧
      IsPowTwo n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] ∧ ∀ r ∈ piSet c.B, r ∣ 2 ^ n - 1

theorem s21_21B_of_s21_21EB {D : Data G} {Ch : Choice2011 G} (he : CFSG.Open.evenRank G ≠ 3)
    (h : S21_21EB D Ch) : S21_21B D Ch :=
  fun h1930 c hB hH _ _ => absurd (h h1930 c hB hH) he

end CFSG.LocalAnalysis.UniquenessCase.UC22
