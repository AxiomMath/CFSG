module

public import CFSG.RankThree.PartOne.S10.Defs
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement Pointwise

@[expose] def TwoActionInputs : Prop :=
  MinimalTwoActionAlternatives ∧ SelectedPrimeMinimalTwoActionReduction ∧
    ElementarySmallActionWholeGroupLifting

@[expose] def SelectedPrimeElementsNormalizeThetaComponents : Prop :=
  (∀ (H : Type) [Group H] [Finite H], evenRank H ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ x : H, (∃ k : ℕ, orderOf x = p ^ k) → ∀ L ∈ thetaComponents p H,
      x ∈ Subgroup.normalizer (L : Set H)) ∧
  (∀ (G : Type) [Group G] [Finite G], evenRank G ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ A : Subgroup G, IsElementaryAbelian p A → ∀ L ∈ thetaComponentFamily p A,
      A ≤ Subgroup.normalizer (L : Set G))

@[expose] def LocalThetaComponentQuotientNormalizationEmbedding : Prop :=
  SchreierFor InCatalog →
  ∀ (H : Type) [Group H] [Finite H], CFSG.IsKGroup H → ∀ p : ℕ, p.Prime →
    ∀ x : H, (∃ k : ℕ, orderOf x = p ^ k) → ∀ Y ∈ thetaComponentsAt p x,
    (∀ L : Subgroup (H ⧸ aschbacherSolvableCore p H), IsComponent L →
      (x : H ⧸ aschbacherSolvableCore p H) ∈ Subgroup.normalizer (L : Set _) ∧
        Y.map (QuotientGroup.mk' (aschbacherSolvableCore p H)) ≤
          Subgroup.normalizer (L : Set _)) →
    ∃ L ∈ thetaComponents p H, Y ≤ L

@[expose] def PCoprimeLocalThetaComponentQuotientNormalizationFrontier : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.IsKGroup H → evenRank H ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ x : H, orderOf x = p → ∀ Y ∈ thetaComponentsAt p x, ¬ p ∣ Nat.card Y →
    ∀ L : Subgroup (H ⧸ aschbacherSolvableCore p H), IsComponent L →
      Y.map (QuotientGroup.mk' (aschbacherSolvableCore p H)) ≤ Subgroup.normalizer (L : Set _)

@[expose] def LocalThetaComponentEmbeddingFrontier : Prop :=
  SchreierFor InCatalog →
  ∀ (H : Type) [Group H] [Finite H], CFSG.IsKGroup H → evenRank H ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ x : H, orderOf x = p → ∀ Y ∈ thetaComponentsAt p x, ∃ L ∈ thetaComponents p H, Y ≤ L

@[expose] def SectionTenTrivialActorComponentSupplement : Prop :=
  SchreierFor InCatalog →
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.IsKProper G → evenRank G ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ A : Subgroup G, IsElementaryAbelian p A → ∀ a ∈ A, a ≠ 1 →
    ∀ L ∈ thetaComponentFamily p A,
      ⁅L, Subgroup.zpowers a⁆ ≤ inSubgroup (aschbacherSolvableCore p) L →
      ∃ K ∈ thetaComponentsAt p a, sectionTenRel p L K

@[expose] def SectionTenComponentSupplementTransitivity : Prop :=
  SchreierFor InCatalog →
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.IsKProper G → evenRank G ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ A : Subgroup G, IsElementaryAbelian p A → ∀ L ∈ thetaComponentFamily p A,
    ∀ K ∈ thetaComponentFamily p A, ∀ J ∈ thetaComponentFamily p A,
      sectionTenRel p L K → sectionTenRel p K J → sectionTenRel p L J

@[expose] def SectionTenHyperplaneLocalResidualObstruction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ L ∈ thetaComponentFamily p A, ∀ B : Subgroup G, B ≤ A → Nat.card B = p ^ 2 →
      ⁅L, B⁆ ≤ inSubgroup (aschbacherSolvableCore p) L →
      ∃ b ∈ B, b ≠ 1 ∧
        inSubgroup perfectResidual
            ((L ⊓ Subgroup.centralizer ({b} : Set G)) ⊔
              inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G))) ∉
          thetaComponentsAt p b

@[expose] def SectionTenMaximalComponentQuotientActorKernelCyclic : Prop :=
  SchreierFor InCatalog →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ L ∈ sectionTenStar p A,
      A ≤ Subgroup.normalizer (L : Set G) ∧ IsCyclic ↥(thetaQuotientCentralizer p A L)

@[expose] def NormalPCoreCentralizingTwoCommutatorProducesThetaComponent : Prop :=
  ∀ (H : Type) [Group H] [Finite H], evenRank H ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ A : Subgroup H, IsPGroup p A → ∀ Q : Subgroup H, IsPGroup 2 Q →
    A ≤ Subgroup.normalizer (Q : Set H) → ⁅Q, A⁆ = Q →
    ⁅A, Q ⊓ aschbacherSolvableCore p H⁆ = ⊥ →
    ⁅Q.map (QuotientGroup.mk' (aschbacherSolvableCore p H)),
      pCore p (H ⧸ aschbacherSolvableCore p H)⁆ = ⊥ →
    ∀ a ∈ A, ⁅Q, Subgroup.zpowers a⁆ ≠ ⊥ →
      ∃ L ∈ thetaComponents p H, A ≤ Subgroup.normalizer (L : Set H) ∧
        ⁅L, Subgroup.zpowers a⁆ = L

@[expose] def SectionTenFiveNormalPCoreTwoGroupWitnessFrontier : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ a ∈ A, a ≠ 1 → ∃ b ∈ A, b ∉ Subgroup.zpowers a ∧ ∃ Q : Subgroup G, IsPGroup 2 Q ∧
      A ≤ Subgroup.normalizer (Q : Set G) ∧ Q ≤ Subgroup.centralizer ({b} : Set G) ∧
      ⁅Q, A⁆ = Q ∧ ⁅Q, Subgroup.zpowers a⁆ ≠ ⊥ ∧
      ⁅(Q.subgroupOf (Subgroup.centralizer ({b} : Set G))).map
          (QuotientGroup.mk' (aschbacherSolvableCore p ↥(Subgroup.centralizer ({b} : Set G)))),
        pCore p (↥(Subgroup.centralizer ({b} : Set G)) ⧸
          aschbacherSolvableCore p ↥(Subgroup.centralizer ({b} : Set G)))⁆ = ⊥

@[expose] def SectionTenFiveActorMovedThetaComponentExistence : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ a ∈ A, a ≠ 1 → ∃ L ∈ thetaComponentFamily p A,
      A ≤ Subgroup.normalizer (L : Set G) ∧ ⁅L, Subgroup.zpowers a⁆ = L

@[expose] def SectionTenMovingTwoStratumUpwardClosure : Prop :=
  ∀ (G : Type) [Group G] [Finite G], evenRank G ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    AschVanishing G p → ∀ A : Subgroup G, IsElementaryAbelian p A → Nat.card A = p ^ 3 →
    ∀ L ∈ thetaComponentFamily p A, ∀ K ∈ thetaComponentFamily p A,
      sectionTenRel p L K → L ∈ sectionTenZero p A → K ∈ sectionTenZero p A

@[expose] def MovingThetaComponentQuasisimplicityReducesToOddCoreCentralization : Prop :=
  ∀ (G : Type) [Group G] [Finite G], evenRank G ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    AschVanishing G p → ∀ A : Subgroup G, IsElementaryAbelian p A → Nat.card A = p ^ 3 →
    ∀ L ∈ sectionTenZero p A,
      A ≤ Subgroup.normalizer (L : Set G) ∧ ⁅L, A⁆ = L ∧
      ⁅inSubgroup (aschbacherSolvableCore p) L, L⁆ ≤ oddThetaCore p L ∧
      (∀ [((oddThetaCore p L).subgroupOf L).Normal],
        CFSG.IsQuasisimple (L ⧸ (oddThetaCore p L).subgroupOf L)) ∧
      (CFSG.IsQuasisimple L ↔ ⁅L, oddThetaCore p L⁆ = ⊥)

@[expose] def NonquasisimpleMovingThetaComponentMinimalOddCoreAction : Prop :=
  ∀ (G : Type) [Group G] [Finite G], evenRank G ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    AschVanishing G p → ∀ A : Subgroup G, IsElementaryAbelian p A → Nat.card A = p ^ 3 →
    ∀ L ∈ sectionTenZero p A, ¬ CFSG.IsQuasisimple L →
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ p ∧ ∃ D R : Subgroup G, D ≠ ⊥ ∧ D ≤ L ∧
      (D.subgroupOf L).Characteristic ∧ D ≤ oddThetaCore p L ∧ (∀ x ∈ D, x ^ q = 1) ∧
      ⁅⁅D, D⁆, D⁆ = ⊥ ∧ IsPGroup 2 R ∧ R ≤ L ∧ A ≤ Subgroup.normalizer (R : Set G) ∧
      ⁅R, A⁆ = R ∧ R ≠ ⊥ ∧ ⁅R, D⁆ ≠ ⊥ ∧
      (∀ U : Subgroup G, U < R → A ≤ Subgroup.normalizer (U : Set G) → ⁅U, A⁆ = U →
        ⁅U, D⁆ = ⊥) ∧
      (A ⊓ Subgroup.centralizer (R : Set G)).relIndex A = p ∧
      (∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3)

@[expose] def NonquasisimpleMovingThetaComponentPrimeCut : Prop :=
  TwoActionInputs →
  ∀ (G : Type) [Group G] [Finite G], evenRank G ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    AschVanishing G p → ∀ A : Subgroup G, IsElementaryAbelian p A → Nat.card A = p ^ 3 →
    ∀ L ∈ sectionTenZero p A, CFSG.IsQuasisimple L ∨ p = 5 ∨ p = 7

@[expose] def NonquasisimpleMovingThetaComponentScalarKernelHyperplane : Prop :=
  TwoActionInputs →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ L ∈ sectionTenZero p A, ¬ CFSG.IsQuasisimple L →
    (p = 5 ∨ p = 7) ∧ (thetaQuotientCentralizer p A L).relIndex A = p ∧
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ p ∧ ∃ D R : Subgroup G, D ≠ ⊥ ∧ D ≤ L ∧
      (D.subgroupOf L).Characteristic ∧ D ≤ oddThetaCore p L ∧ (∀ x ∈ D, x ^ q = 1) ∧
      ⁅⁅D, D⁆, D⁆ = ⊥ ∧ IsPGroup 2 R ∧ R ≤ L ∧ A ≤ Subgroup.normalizer (R : Set G) ∧
      ⁅R, A⁆ = R ∧ R ≠ ⊥ ∧ ⁅R, D⁆ ≠ ⊥ ∧
      A ⊓ Subgroup.centralizer (R : Set G) = thetaQuotientCentralizer p A L ∧
      (∀ U : Subgroup G, U < R → A ≤ Subgroup.normalizer (U : Set G) → ⁅U, A⁆ = U →
        ⁅U, D⁆ = ⊥) ∧
      (∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3) ∧
      ∀ e ∈ thetaQuotientCentralizer p A L,
        ∃ k : ℕ, ∀ d ∈ D, (e * d * e⁻¹)⁻¹ * d ^ k ∈ inSubgroup frattini D

@[expose] def SectionTenMaximalMovingThetaComponentsQuasisimple : Prop :=
  SchreierFor InCatalog → TwoActionInputs →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ L ∈ sectionTenZeroStar p A, CFSG.IsQuasisimple L

@[expose] def SectionTenFiveCriticalActionAndCentralInvolution : Prop :=
  TwoActionInputs →
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G), c ∈ A → c ≠ 1 →
    SteinbergBM.SectionTenSetup G 5 A → L ∈ sectionTenAt 5 (sectionTenZero 5 A) c →
    ¬ CFSG.IsQuasisimple L →
    ∃ (q : ℕ) (D R : Subgroup G), D ≤ L ∧ R ≤ L ∧ FiveCriticalData A L c q D R

end CFSG.RankThree.PartOne
