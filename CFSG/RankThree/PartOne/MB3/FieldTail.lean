module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Foundations.Basic
public import CFSG.RankThree.GroupTheory.SteinbergCEAschbacherPrimeSelector
public import CFSG.RankThree.LocalRank.SelectorCases

public section

namespace CFSG.RankThree.PartOne.MB3

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def FieldComponentsLn2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (n : ℕ), (n = 6 ∨ n = 7) →
    StatedClassicalModel ↥L .PSL n 2 1 → ∀ b ∈ L, orderOf b = 7 → ∀ E : Subgroup G,
      E ≤ L ⊓ Subgroup.centralizer ({b} : Set G) →
      CFSG.IsComponent (E.subgroupOf (L ⊓ Subgroup.centralizer ({b} : Set G))) →
      StatedClassicalModel ↥E .PSL (n - 3) 2 1 ∨ StatedClassicalModel ↥E .PSL 2 2 3

end CFSG.RankThree.PartOne.MB3
