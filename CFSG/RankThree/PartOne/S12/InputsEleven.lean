module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.GroupTheory.SteinbergBMSectionTenSetup
public import CFSG.RankThree.GroupTheory.SteinbergCESectionTenStrata

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.Blueprint (LieModel EvenLieType)
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def InducesFieldAut (p : ℕ) (a : G) (J : Subgroup G) : Prop :=
  a ∈ Subgroup.normalizer (J : Set G) ∧ a ∉ J ⊔ Subgroup.centralizer (J : Set G) ∧
    a ^ p ∈ J ⊔ Subgroup.centralizer (J : Set G) ∧
    ∃ (t : StatedLieTag) (n f : ℕ), 1 ≤ f ∧ LieModel (J ⧸ Subgroup.center J) t n 2 (p * f) ∧
      (LieModel (↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({a} : Set G))) ⧸
        Subgroup.center ↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({a} : Set G))))
        t n 2 f ∨
      (t = .twistedF4 ∧ n = 0 ∧ f = 1 ∧
        LieModel (↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({a} : Set G))) ⧸
          Subgroup.center ↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({a} : Set G))))
          .Tits 0 2 1))

@[expose] def InSec11Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ c ∈ A, c ≠ 1 → ∀ J ∈ sectionTenAt p (sectionTenZeroStar p A ∩ sectionTenTwo p A) c,
      EvenLieType (J ⧸ Subgroup.center J) ∧ ¬ p ∣ Nat.card (Subgroup.center J) ∧
      ∃ a d : G, a ∈ A ∧ d ∈ A ∧ d ≠ 1 ∧
        A = Subgroup.zpowers a ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers d ∧
        Subgroup.zpowers d = A ⊓ J ∧ InducesFieldAut p a J

@[expose] def KF128 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (J E : Subgroup G) (a d : G),
    p.Prime → 5 ≤ p → CFSG.IsQuasisimple J → EvenLieType (J ⧸ Subgroup.center J) →
    evenRank ↥J ≤ 3 → ¬ p ∣ Nat.card (Subgroup.center J) → IsElementaryAbelian p E →
    E ≤ Subgroup.normalizer (J : Set G) → a ∈ E → d ∈ E → d ∈ J → d ≠ 1 →
    InducesFieldAut p a J →
    (∃ S : Subgroup G, S ≤ J ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
      a ∈ Subgroup.normalizer (S : Set G) ∧ d ∈ Subgroup.normalizer (S : Set G)) →
    ∃ y ∈ J, (∃ k : ℕ, orderOf y = p ^ k) ∧ y * d * y⁻¹ = d ∧ y * a * y⁻¹ ≠ a ∧
      ∀ e ∈ E, y * e * y⁻¹ * e⁻¹ ∈ Subgroup.zpowers d

end CFSG.RankThree.PartOne
