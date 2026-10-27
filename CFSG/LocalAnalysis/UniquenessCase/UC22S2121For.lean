module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2121B

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Hyp2120For (D : Data G) (X : Subgroup G) : Prop :=
  ⁅Hinf D.M, oTwoFOf D.M⁆ ≤ CFSG.Open.pCoreOf 2 D.M ∧
  (∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal ∧
    ¬ ∃ n : ℕ, Odd n ∧ (IsSp4 (Bar2 L) n ∨ IsSU3 (Bar2 L) n)) ∧
  (∀ p ∈ D.sig, ∃ P : Subgroup G,
    CFSG.ABGLocalTools.IsSylowOf p P (barPreimage D.M (centE D.M)) ∧
      P ≤ normalizer (X : Set G)) ∧
  (∀ p ∈ D.sig, 1 < CFSG.Open.pRank p (barPreimage D.M (centE D.M)) →
    ¬ InvertedIn D.M X)

@[expose] def S21_21For (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calL D.T D.M, ∀ X ∈ calB1 D.T D.M L,
    X ≤ D.M → X ≠ ⊥ → Hyp2120For D X → ∀ p ∈ D.sig,
    Hinf D.M = Opp p (oTwoEOf D.M) ∧ CFSG.Open.evenRank G = 3 ∧
    ∃ n : ℕ,
      ((IsL2Square (Bar2 (Opp p (oTwoEOf D.M))) n ∧
          CFSG.Open.pRank p (Opp p (barPreimage D.M (centE D.M))) = 1) ∨
        ((∃ (A B : Type) (_ : Group A) (_ : Group B),
            Nonempty (Bar2 (Opp p (oTwoEOf D.M)) ≃* A × B) ∧ IsU3 A n ∧ IsL2 B n) ∧
          Opp p (barPreimage D.M (centE D.M)) = ⊥)) ∧
      IsPowTwo n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] ∧ ∀ r ∈ piSet X, r ∣ 2 ^ n - 1

theorem s21_21B_of_s21_21For {D : Data G} {Ch : Choice2011 G} (h : S21_21For D Ch) :
    S21_21B D Ch :=
  fun h1930 c hB hH p hp =>
    h h1930 c c.L0 c.hL0.1 c.B c.hB (c.hle.trans c.hBM) hB hH p hp

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
