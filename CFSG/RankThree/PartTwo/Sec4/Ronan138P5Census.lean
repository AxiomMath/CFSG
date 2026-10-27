module

public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Census


@[expose] def K419UnitaryCensusCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsComponent L →
    IsList46 (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ a ∈ Subgroup.normalizer (L : Set G), orderOf a = 3 →
    a ∉ Subgroup.centralizer (L : Set G) →
    ∀ Y : Subgroup G, Y ≤ L ⊓ Subgroup.centralizer ({a} : Set G) → Group.IsPerfect Y →
      (Y.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))).IsSubnormal →
    ∀ (m : ℕ) (π : Y →* projSU 3 2 m), Odd m → 1 < m → Function.Surjective π →
      Nat.Coprime (Nat.card π.ker) 3 →
      (∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 (3 * m) K),
          InducesKindPSU3 h L a .field) ∨
      (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ m) ^ 3 ∧
        ∃ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ m) ∧ InducesKindTriality σ L a .graphField)

end Census

end CFSG.RankThree.PartTwo.Sec4
