module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def S20_14C (D : Data G) : Prop :=
  H1930 D → ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M →
    ∀ H ∈ hSet D.T D.M, p ∣ Nat.card ↥(H ⊓ D.M) →
      Opp p H ∈ calLStar D.T D.M ∧
      ∃ m n : ℕ, 2 < m ∧ m ≤ 4 ∧ 2 < n ∧
        CFSG.Open.IsQuasisimple (Bar2 (Opp p H)) ∧
        LieModel (Bar2 (Opp p H) ⧸ Subgroup.center (Bar2 (Opp p H))) .PSL m 2 n ∧
        2 ^ (n * (m - 1)) ≡ 1 [MOD p] ∧ ¬ 2 ^ n ≡ 1 [MOD p] ∧
        Nonempty (↥(Opp p (⊤ : Subgroup (Bar2 (H ⊓ D.M)))) ≃*
          CFSG.Open.StatedSL (m - 1) (GaloisField 2 n))

@[expose] def S22FinA (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx22b D Ch, ∀ p ∈ D.sig, ∀ H ∈ hSet D.T D.M,
    centralizer (D.Z : Set G) ≤ H → D.M ⊓ centralizer (c.V : Set G) ≤ H →
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M → ∀ m : ℕ, 2 < m →
    CFSG.Open.IsQuasisimple (Bar2 (Opp p H)) →
    LieModel (Bar2 (Opp p H) ⧸ Subgroup.center (Bar2 (Opp p H))) .PSL 3 2 m →
    Opp p (H ⊓ D.M) ∈ calC (D.M ⊓ centralizer (c.V : Set G)) →
    Nonempty (Bar2 (Opp p (H ⊓ D.M)) ≃* CFSG.Open.StatedSL 2 (GaloisField 2 m)) →
      ∃ A : Subgroup G, c.B0 ≤ A ∧ A ≤ D.M ⊓ Opp p H ∧ IsMulCommutative A ∧
        A ⊓ Opp p (H ⊓ D.M) ⊔ c.B0 = A ∧ A ⊓ Opp p (H ⊓ D.M) ⊓ c.B0 = ⊥ ∧
        Nonempty (↥(A ⊓ Opp p (H ⊓ D.M)) ≃* ↥c.B0)

end CFSG.LocalAnalysis.UniquenessCase.UC22
