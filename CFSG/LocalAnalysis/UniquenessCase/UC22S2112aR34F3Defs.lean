module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Defs
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.LocalAnalysis.UniquenessCase.UCFront14

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.LocalAnalysis.UniquenessCase (fundPred)
open scoped Pointwise

@[expose] def KFieldAutOdd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : StatedLieTag) (n p f r : ℕ),
    p.Prime → p ≠ 2 → StatedLieAdmissible t n p f → LieModel X t n p f →
    ¬ (t = .PSL ∧ n = 2) → t ≠ .twistedG2 → r.Prime → 5 ≤ r →
    ¬ r ∣ (genericOrders t n p f).1 →
    ∀ θ : MulAut X, orderOf θ = r → θ ∉ (MulAut.conj : X →* MulAut X).range →
      r ∣ f ∧ ∃ Y : Subgroup X, Y ≤ signalizerFixedSubgroup θ ∧ IsSimpleGroup Y ∧
        2 ≤ pRank p Y


@[expose] def KFunCount : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : StatedLieTag) (n p f : ℕ),
    p.Prime → p ≠ 2 → StatedLieAdmissible t n p f → LieModel X t n p f → ∀ P : Sylow 2 X,
      (FunTwoType t n → (FunSet (fundPred (p ^ f)) X (P : Subgroup X)).ncard = 2) ∧
      (FunManyType t n → 3 ≤ (FunSet (fundPred (p ^ f)) X (P : Subgroup X)).ncard)

@[expose] def KFunSplit : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : StatedLieTag) (n p f : ℕ),
    p.Prime → p ≠ 2 → StatedLieAdmissible t n p f → LieModel X t n p f →
    ¬ (t = .PSL ∧ n = 2) → t ≠ .twistedG2 → ∀ (P : Sylow 2 X) (B : Subgroup X), B ≠ ⊥ →
      IsMulCommutative B → Odd (Nat.card B) → ¬ 3 ∣ Nat.card B → ¬ p ∣ Nat.card B →
      (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X) →
      (∀ s : ℕ, s.Prime → s ∣ Nat.card B → pRank s B ≤ 2 ∧ pRank s (⊤ : Subgroup X) ≤ 3) →
      ∀ K ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X),
        B = (B ⊓ K) ⊔ (B ⊓ centralizer (K : Set X))

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_12aFR34F3Q35 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n p f → FunManyType t n →
    p ^ f ≤ 5 → LieModel (BarInf L) t n p f → (∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) → F08.Thin8 L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
