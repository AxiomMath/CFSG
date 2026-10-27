module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Local
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG
open scoped MatrixGroups

@[expose] def PrimeThreeLinear : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Group.IsPerfect Y →
    Subgroup.centralizer (pCore 3 Y : Set Y) ≤ pCore 3 Y → CFSG.pRank 3 Y ≤ 3 →
      pCore 3 Y ≠ ⊤ →
        Nonempty (Y ⧸ pCore 3 Y ≃* SL(3, ZMod 3)) ∨ Nonempty (Y ⧸ pCore 3 Y ≃* SL(2, ZMod 5))

@[expose] def PartTwoRankTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → Group.IsPerfect G →
    ∀ (K : Subgroup G) [K.Normal], Group.IsSolvable K → IsSimpleGroup (G ⧸ K) →
      ¬ 3 ∣ Nat.card K → pCore 2 G = ⊥ → ¬ IsQuasisimple G →
        CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ 2 →
          IsQuasisimple (G ⧸ oddCore G) ∨
            IsExtOf (G ⧸ oddCore G) (alternatingGroup (Fin 5)) Q8D8

@[expose] def PartTwoRankThreeHyp (G : Type) [Group G] [Finite G] (K : Subgroup G) [K.Normal] :
    Prop :=
  SectionFourHyp G ∧ Group.IsPerfect G ∧ Group.IsSolvable K ∧ IsSimpleGroup (G ⧸ K) ∧
    ¬ 3 ∣ Nat.card K ∧ pCore 2 G = ⊥ ∧ ¬ IsQuasisimple G ∧
    CFSG.Open.pRank 2 (⊤ : Subgroup G) = 3 ∧
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ Subgroup.centralizer (pCore p G : Set G) ≤ K ∧
      ∃ D : Subgroup G, CriticalAt p D ∧ Odd (Nat.card (Subgroup.centralizer (D : Set G)))

@[expose] def PartTwoRankThreeNotQuasisimple : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) [K.Normal], PartTwoRankThreeHyp G K →
    ¬ IsQuasisimple (G ⧸ oddCore G)

@[expose] def PartTwoRankThreeEndgame : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) [K.Normal], PartTwoRankThreeHyp G K →
    ¬ IsQuasisimple (G ⧸ oddCore G) →
      IsExtOf (G ⧸ oddCore G) (alternatingGroup (Fin 5)) Q8D8 ∨
        IsExtOf (G ⧸ oddCore G) (alternatingGroup (Fin 5)) Z4Q8Q8 ∨
        IsExtOf (G ⧸ oddCore G) (alternatingGroup (Fin 6)) Z4Q8Q8

end CFSG.RankThree.PartTwo.Sec4.Census
