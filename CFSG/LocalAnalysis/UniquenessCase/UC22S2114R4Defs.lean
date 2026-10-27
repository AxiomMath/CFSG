module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21c
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)

variable {G : Type} [Group G] [Finite G]

@[expose] def KLieBorelAutPrime : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (m f : ℕ),
    StatedLieAdmissible t m 2 f → LieModel X t m 2 f → 3 ≤ PartTwo.S17.CS17LieRank t m →
    ∀ U : Subgroup X, IsSylowTwoOf U ⊤ → ∀ r : ℕ, r.Prime → 5 ≤ r → ¬ r ∣ f →
      ∀ α : MulAut X, α ≠ 1 → α ^ r = 1 → U.map α.toMonoidHom = U →
        r ∣ 2 ^ (2 * f) - 1 ∧ (t ≠ .PSU → t ≠ .POmegaMinus → t ≠ .twistedE6 → r ∣ 2 ^ f - 1)

@[expose] def S21_14R4F (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    ∀ l f : ℕ, 4 ≤ l → PartTwo.S17.CHasLieRank (BarInf L) l f → 3 ≤ c.n →
    c.B0 ≤ normalizer (L : Set G) → (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
    (Odd c.n ∨ (LieModel (BarInf L) .PSL 5 2 f ∧ Odd f ∧ 3 ≤ f)) →
    (∀ r : ℕ, r.Prime → 5 ≤ r → r ∣ 2 ^ c.n - 1 → r ∣ f) →
      LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1

end CFSG.LocalAnalysis.UniquenessCase.UC22
