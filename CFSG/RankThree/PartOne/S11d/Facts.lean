module

public import CFSG.RankThree.PartOne.S11b.Sec109

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

@[expose] def BenderPCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L B : Subgroup G) (n : ℕ),
    Sec109.Config p A c L B n → ∀ (b : G) (S : Subgroup G), Sec109.Witness A c B b S →
      ⁅(S.subgroupOf (Subgroup.centralizer ({b} : Set G))).map
          (QuotientGroup.mk' (aschbacherSolvableCore p ↥(Subgroup.centralizer ({b} : Set G)))),
        pCore p (↥(Subgroup.centralizer ({b} : Set G)) ⧸
          aschbacherSolvableCore p ↥(Subgroup.centralizer ({b} : Set G)))⁆ = ⊥

@[expose] def MaximalBranchThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L B : Subgroup G) (n : ℕ),
    Sec109.Config p A c L B n → ∀ (b : G) (S K K' : Subgroup G) (a' : G),
      Sec109.Witness A c B b S → K ∈ sectionTenAt p (sectionTenZero p A) b → S ≤ K →
      K' ∈ sectionTenAt p (sectionTenZeroStar p A) a' → a' ∈ A → a' ∉ B →
      sectionTenRel p K K' → False

end CFSG.RankThree.PartOne
