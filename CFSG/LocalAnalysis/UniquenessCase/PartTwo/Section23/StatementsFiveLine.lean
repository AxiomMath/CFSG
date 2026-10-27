module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

@[expose] def S23_5_line (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch,
    IsL2 (Bar2 c.L0) (CFSG.Open.pRank 2 D.Z) ∨
    (c.L = c.L0 ∧ IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z) ∧
      IsL2 (Bar2 c.L0) (2 * CFSG.Open.pRank 2 D.Z) ∧
      piSet (c.B ⊓ Subgroup.centralizer (D.Z : Set G)) =
        piSet c.B ∩ {p | p.Prime ∧ p ∣ 2 ^ CFSG.Open.pRank 2 D.Z + 1}) ∨
    (c.L = c.L0 ∧ IsL2Square (Bar2 c.L0) (CFSG.Open.pRank 2 D.Z) ∧
      IsCyclic ↥(c.B ⊓ Subgroup.centralizer (D.Z : Set G)) ∧
      ∀ E : Subgroup G, E ≤ c.B → E ⊓ Subgroup.centralizer (D.Z : Set G) = ⊥ →
        IsCyclic ↥E)

@[expose] def S23_5_lineOmegaPlus (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, IsL2Square (Bar2 c.L0) (CFSG.Open.pRank 2 D.Z) →
    c.L = c.L0 ∧
    (∀ A : Subgroup G, A ≤ c.L0 → IsMulCommutative A → Odd (Nat.card A) → Permutes A D.T →
      IsCyclic ↥(A ⊓ Subgroup.centralizer (D.Z : Set G))) ∧
    c.L0 ⊓ Subgroup.normalizer ((D.T ⊓ c.L0 : Subgroup G) : Set G) ≤
      Subgroup.normalizer (D.Z : Set G)

@[expose] def S23_5_lineL2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch,
    (IsL2 (Bar2 c.L0) (CFSG.Open.pRank 2 D.Z) ∧
        c.B ⊓ Subgroup.centralizer (D.Z : Set G) = ⊥) ∨
      IsL2 (Bar2 c.L0) (2 * CFSG.Open.pRank 2 D.Z) ∨
      IsL2Square (Bar2 c.L0) (CFSG.Open.pRank 2 D.Z)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
