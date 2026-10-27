module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_12aFR34L3P (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 →
    (LieModel (BarInf L) .PSL 3 p 1 ∨ LieModel (BarInf L) .PSU 3 p 1) →
    (∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) → F08.Thin8 L

@[expose] def S21_12aFR34L3E (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, Even c.n → ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ f : ℕ, 2 ≤ f → (LieModel (BarInf L) .PSL 3 p f ∨ LieModel (BarInf L) .PSU 3 p f) →
    (∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) → F08.Thin8 L

@[expose] def S21_12aFR34F2Q35 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n p f → FunTwoType t n →
    p ^ f ≤ 5 → LieModel (BarInf L) t n p f → (∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) → F08.Thin8 L

@[expose] def S21_12aFR34F2Sig (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ D.sig →
    ∀ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n p f → FunTwoType t n →
    7 ≤ p ^ f → LieModel (BarInf L) t n p f → (∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) → F08.Thin8 L

@[expose] def S21_12aFR34F2Even (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, Even c.n → ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 →
    p ∈ D.sig → ∀ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n p f →
    FunTwoType t n → 7 ≤ p ^ f → (f = 1 ∨ (c.n = 4 ∧ 5 ∣ (genericOrders t n p f).1)) →
    LieModel (BarInf L) t n p f → (∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) → F08.Thin8 L

end CFSG.LocalAnalysis.UniquenessCase.UC22
