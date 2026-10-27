module

public import CFSG.RankThree.PartOne.S12.Hyp
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

@[expose] def InSec10Seven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ L ∈ sectionTenZeroStar p A, CFSG.Blueprint.EvenLieType (L ⧸ Subgroup.center L)

@[expose] def InSec10Nine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ L ∈ sectionTenZeroStar p A, ∀ n : ℕ, ¬ StatedClassicalModel ↥L .PSL n 2 1

@[expose] def KF122 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → 5 ≤ p → ∀ L : Subgroup G,
    CFSG.IsQuasisimple L → CFSG.Blueprint.EvenLieType (L ⧸ Subgroup.center L) →
    ¬ p ∣ Nat.card (Subgroup.center L) → localRank p L = 2 → evenRank ↥L ≤ 3 →
    (∃ A₀ : Subgroup G, A₀ ≤ L ∧ IsElementaryAbelian p A₀ ∧ Nat.card A₀ = p ^ 2 ∧
      ∃ S : Subgroup G, S ≤ L ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
        A₀ ≤ Subgroup.normalizer (S : Set G) ∧ S = ⁅S, A₀⁆) →
    ∀ x : G, x ∈ Subgroup.normalizer (L : Set G) → x ^ p = 1 →
      x ∉ L ⊔ Subgroup.centralizer (L : Set G) → 3 ≤ localRank p ↥(L ⊔ Subgroup.zpowers x)

@[expose] def InSU5Contained : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → p ∣ Nat.card (Subgroup.center L) → E ≤ L

@[expose] def InSec10FivePlus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ a ∈ A, a ≠ 1 → ∃ L ∈ sectionTenZero p A,
      A ≤ Subgroup.normalizer (L : Set G) ∧ ⁅L, Subgroup.zpowers a⁆ = L

end CFSG.RankThree.PartOne
