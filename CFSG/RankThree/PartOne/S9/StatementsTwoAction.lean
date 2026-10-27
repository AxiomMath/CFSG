module

public import CFSG.RankThree.PartOne.S9.Defs
public import CFSG.LocalAnalysis.SectionRank.Ccomm.CriticalDefinition
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.SectionRank.Ccomm
open scoped commutatorElement Pointwise

@[expose] def ElementaryFaithfulQuotientKernelElimination : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p q d : ℕ) (A D R X : Subgroup G),
    p.Prime → q.Prime → 3 < p → q ≠ 2 → p ≠ q → ((p = 7 ∧ d = 3) ∨ (p = 5 ∧ d = 4)) →
    IsElementaryAbelian p A → Nat.card A = p ^ 2 → IsPGroup 2 R →
    A ≤ Subgroup.normalizer (R : Set G) → R ⊔ A ≤ Subgroup.normalizer (D : Set G) →
    IsPGroup q D → (∀ x ∈ D, x ^ q = 1) → ⁅⁅D, D⁆, D⁆ = ⊥ →
    (∀ r ∈ R, r ≠ 1 →
      CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3) →
    X ≤ D → IsFrattiniIrreducibleFor (R ⊔ A) X →
    ⁅R, R⁆ ≤ R ⊓ Subgroup.centralizer (X : Set G) →
    (∀ r ∈ R, r ^ 2 ∈ R ⊓ Subgroup.centralizer (X : Set G)) →
    (R ⊓ Subgroup.centralizer (X : Set G)).relIndex R = 2 ^ d →
    (∀ Y : Subgroup G, R ⊓ Subgroup.centralizer (X : Set G) ≤ Y → Y ≤ R →
      A ≤ Subgroup.normalizer (Y : Set G) →
      Y = R ⊓ Subgroup.centralizer (X : Set G) ∨ Y = R) →
    Nat.card (A ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) = p →
    R ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧ IsElementaryAbelian 2 R ∧ Nat.card R = 2 ^ d ∧
    (inSubgroup frattini X).relIndex X = q ^ p ∧ 4 ≤ CFSG.pRank q X ∧
    (∃ r ∈ R, r ≠ 1 ∧ CFSG.pRank q ↥(X ⊓ Subgroup.centralizer ({r} : Set G)) = 3 ∧
      CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) = 3) ∧
    (p = 7 → ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(X ⊓ Subgroup.centralizer ({r} : Set G)) = 3 ∧
      CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) = 3) ∧
    (p = 5 → 10 ≤ Set.ncard {r : G | r ∈ R ∧ r ≠ 1 ∧
      CFSG.pRank q ↥(X ⊓ Subgroup.centralizer ({r} : Set G)) = 3 ∧
      CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) = 3}) ∧
    (⁅A ⊓ Subgroup.centralizer (R : Set G), X⁆ = ⊥ ∨ q % p = 1)

@[expose] def MinimalTwoActionSmallFaithfulQuotient : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p q : ℕ) (A D R : Subgroup G),
    MinTwoActionSetting p q A D R →
    (∀ r ∈ R, r ≠ 1 →
      CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3) →
    ∃ X : Subgroup G, X ≤ D ∧ ⁅X, R⁆ = X ∧ IsFrattiniIrreducibleFor (R ⊔ A) X ∧
      X ⊓ inSubgroup frattini D = inSubgroup frattini X ∧
      R ⊓ Subgroup.centralizer (X : Set G) ≤ inSubgroup frattini R ∧
      (∃ a ∈ A, ∃ r ∈ R, ⁅a, r⁆ ∉ inSubgroup frattini R) ∧
      (∀ Y : Subgroup G, inSubgroup frattini R ≤ Y → Y ≤ R →
        A ≤ Subgroup.normalizer (Y : Set G) → Y = inSubgroup frattini R ∨ Y = R) ∧
      (∀ a ∈ A, ∀ r ∈ inSubgroup frattini R, ⁅a, r⁆ ∈ R ⊓ Subgroup.centralizer (X : Set G)) ∧
      ((p = 7 ∧ ⁅R, R⁆ ≤ R ⊓ Subgroup.centralizer (X : Set G) ∧
          (∀ r ∈ R, r ^ 2 ∈ R ⊓ Subgroup.centralizer (X : Set G)) ∧
          (R ⊓ Subgroup.centralizer (X : Set G)).relIndex R = 8) ∨
        (p = 5 ∧ ⁅R, R⁆ ≤ R ⊓ Subgroup.centralizer (X : Set G) ∧
          (∀ r ∈ R, r ^ 2 ∈ R ⊓ Subgroup.centralizer (X : Set G)) ∧
          (R ⊓ Subgroup.centralizer (X : Set G)).relIndex R = 16) ∨
        (p = 5 ∧ ∃ φ : ↥R →* QD32, Function.Surjective φ ∧
          φ.ker = (R ⊓ Subgroup.centralizer (X : Set G)).subgroupOf R)) ∧
      Nat.card (A ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) = p ∧
      (∀ a ∈ A, (∀ r ∈ R, ⁅a, r⁆ ∈ R ⊓ Subgroup.centralizer (X : Set G)) →
        a ∈ Subgroup.centralizer (R : Set G)) ∧
      (∀ a ∈ A, (∀ r ∈ R, ⁅a, r⁆ ∈ inSubgroup frattini R) →
        a ∈ Subgroup.centralizer (R : Set G)) ∧
      ∀ r ∈ R, r ∉ R ⊓ Subgroup.centralizer (X : Set G) →
        CFSG.pRank q ↥(X ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3

@[expose] def ExtraspecialThirtyTwoFixedRankTwoAction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (q : ℕ) (A R D : Subgroup G), q.Prime → q ≠ 2 → q ≠ 5 →
    IsElementaryAbelian 5 A → Nat.card A = 25 → A ≤ Subgroup.normalizer (R : Set G) →
    IsExtraspecialPGroup 2 R → Nat.card R = 32 →
    (∃ a ∈ A, ∀ r ∈ R, r ∉ inSubgroup Subgroup.center R → ⁅a, r⁆ ∉ inSubgroup Subgroup.center R) →
    R ⊔ A ≤ Subgroup.normalizer (D : Set G) → IsPGroup q D → (∀ x ∈ D, x ^ q = 1) →
    ⁅⁅D, D⁆, D⁆ = ⊥ → R ⊓ Subgroup.centralizer (D : Set G) = ⊥ →
    (∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2) →
    ⁅D, R⁆ = D ∧ (inSubgroup frattini D).relIndex D = q ^ 4 ∧ IsQDShape q D

@[expose] def MinimalTwoActionWithoutRankThreeFixedGroup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p q : ℕ) (A D R : Subgroup G),
    MinTwoActionSetting p q A D R →
    (∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2) →
    p = 5 ∧ Nonempty (R ≃* QD32) ∧ ⁅D, R⁆ = D ∧ IsQDShape q D

@[expose] def ElementarySmallActionWholeGroupLifting : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p q d : ℕ) (A D R : Subgroup G),
    p.Prime → q.Prime → q ≠ 2 → q ≠ p → ((p = 7 ∧ d = 3) ∨ (p = 5 ∧ d = 4)) →
    IsElementaryAbelian p A → Nat.card A = p ^ 2 → A ≤ Subgroup.normalizer (R : Set G) →
    IsElementaryAbelian 2 R → Nat.card R = 2 ^ d →
    Nat.card (A ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) = p →
    (∀ Y : Subgroup G, Y ≤ R → A ≤ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = R) →
    R ⊔ A ≤ Subgroup.normalizer (D : Set G) → IsPGroup q D → (∀ x ∈ D, x ^ q = 1) →
    ⁅⁅D, D⁆, D⁆ = ⊥ → ⁅R, D⁆ ≠ ⊥ →
    (∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3) →
    R ⊓ Subgroup.centralizer (D : Set G) = ⊥ ∧ IsElementaryAbelian q D ∧ Nat.card D = q ^ p ∧
    ⁅D, R⁆ = D ∧ D ⊓ Subgroup.centralizer (R : Set G) = ⊥ ∧ IsFrattiniIrreducibleFor (R ⊔ A) D ∧
    (p = 7 → ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) = 3) ∧
    (p = 5 →
      Set.ncard {r : G | r ∈ R ∧ r ≠ 1 ∧
        CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) = 3} = 10 ∧
      Set.ncard {r : G | r ∈ R ∧ r ≠ 1 ∧
        CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) = 1} = 5) ∧
    (⁅A ⊓ Subgroup.centralizer (R : Set G), D⁆ = ⊥ ∨ q % p = 1)

@[expose] def MinimalFiveActionSmallFieldKernelCentralization : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (q : ℕ) (A D R : Subgroup G),
    MinTwoActionSetting 5 q A D R → (q % 5 = 2 ∨ q % 5 = 3) →
    (∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3) →
    ⁅A ⊓ Subgroup.centralizer (R : Set G), D⁆ = ⊥

@[expose] def MinimalTwoActionAlternatives : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p q : ℕ) (A D R : Subgroup G),
    MinTwoActionSetting p q A D R →
    (∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3) →
    ((((p = 5 ∧ IsElementaryAbelian 2 R ∧ Nat.card R = 16) ∨
        (p = 7 ∧ IsElementaryAbelian 2 R ∧ Nat.card R = 8)) ∧
      (∃ r ∈ R, r ≠ 1 ∧ CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) = 3) ∧
      ⁅D, R⁆ = D ∧ (inSubgroup frattini D).relIndex D = q ^ p ∧
      (⁅A ⊓ Subgroup.centralizer (R : Set G), D⁆ = ⊥ ∨ q % p = 1)) ∨
    (p = 5 ∧ (∃ r ∈ R, r ≠ 1 ∧ CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) = 3) ∧
      (7 < q ∨ ⁅A ⊓ Subgroup.centralizer (R : Set G), D⁆ = ⊥)) ∨
    (p = 5 ∧ Nonempty (R ≃* QD32) ∧ ⁅D, R⁆ = D ∧ IsQDShape q D))

@[expose] def SelectedPrimeMinimalTwoActionReduction : Prop :=
  ∀ (G : Type) [Group G] [Finite G], evenRank G = 3 → ∀ p : ℕ, p.Prime → p ∈ sigmaA G → 3 < p →
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → ∀ A R D : Subgroup G, IsElementaryAbelian p A →
    A ≤ Subgroup.normalizer (R : Set G) → IsPGroup 2 R → ⁅R, A⁆ = R → R ≠ ⊥ →
    R ⊔ A ≤ Subgroup.normalizer (D : Set G) → IsPGroup q D → (∀ x ∈ D, x ^ q = 1) →
    ⁅⁅D, D⁆, D⁆ = ⊥ → ⁅R, D⁆ ≠ ⊥ →
    (A ⊓ Subgroup.centralizer (R : Set G)).relIndex A = p →
    p ≤ Nat.card (A ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) →
    (∀ U : Subgroup G, U < R → A ≤ Subgroup.normalizer (U : Set G) → ⁅U, A⁆ = U →
      U ≤ Subgroup.centralizer (D : Set G)) →
    GoodGlobalRank G p →
    p ≤ 7 ∧ (⁅A ⊓ Subgroup.centralizer (R : Set G), D⁆ = ⊥ ∨
      (p = 5 ∧ Nonempty (R ≃* QD32) ∧ R ⊓ Subgroup.centralizer (D : Set G) = ⊥ ∧
        ⁅D, R⁆ = D ∧ ⁅D, A ⊓ Subgroup.centralizer (R : Set G)⁆ = D ∧ q % 5 = 1 ∧
        localRank q G ≤ 2 ∧ IsQDShape q D))

@[expose] def CriticalQuaternionDihedralOvergroupRigidity : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P A T S : Subgroup G), IsPGroup 2 P → Odd (Nat.card A) →
    A ≤ Subgroup.normalizer (P : Set G) → ⁅P, A⁆ = P → T ≤ P →
    ThompsonCritical (T.subgroupOf P) → S ≤ T → A ≤ Subgroup.normalizer (S : Set G) →
    Nonempty (S ≃* QD32) → IsCyclic ↥(P ⊓ Subgroup.centralizer (S : Set G)) → P = S

@[expose] def QuaternionDihedralAutomorphismPrimeSupport : Prop :=
  ∀ (S : Type) [Group S], Nonempty (S ≃* QD32) →
    Nat.card (MulAut S) ∣ 2 ^ 7 * 3 * 5 ∧
    ∀ (q : ℕ) (P : Type) [Group P] [Finite P], q.Prime → 5 < q → IsPGroup q P →
      ∀ f : P →* MulAut S, f = 1

@[expose] def QuaternionDihedralOddCentralizerGeometry : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (q : ℕ), q.Prime → q ≠ 2 → ∀ S D B : Subgroup G,
    Nonempty (S ≃* QD32) → S ≤ Subgroup.normalizer (D : Set G) →
    B ≤ Subgroup.normalizer (D : Set G) → B ≤ Subgroup.centralizer (S : Set G) →
    S ⊓ Subgroup.centralizer (D : Set G) = ⊥ → ⁅S, inSubgroup frattini D⁆ = ⊥ →
    IsQDShape q D → ∀ z ∈ S, z ≠ 1 → z ∈ inSubgroup Subgroup.center S →
    ∀ r ∈ S, orderOf r = 2 → r ∉ inSubgroup Subgroup.center S →
    ∀ F : Subgroup G, F = D ⊓ Subgroup.centralizer ({r} : Set G) →
      ((IsElementaryAbelian q D ∧ Nat.card D = q ^ 4) →
        IsElementaryAbelian q F ∧ Nat.card F = q ^ 2) ∧
      (¬ (IsElementaryAbelian q D ∧ Nat.card D = q ^ 4) →
        (∀ x ∈ F, x ^ q = 1) ∧ Nat.card F = q ^ 3 ∧ F ⊓ Subgroup.centralizer (F : Set G) = ⁅F, F⁆ ∧
          ⁅F, F⁆ = inSubgroup frattini F ∧ inSubgroup frattini F = inSubgroup frattini D ∧
          Nat.card (inSubgroup frattini D) = q) ∧
      ∀ Y : Subgroup G, Y ≤ F → Nat.card Y = q → ¬ Y ≤ inSubgroup frattini D →
        3 ≤ CFSG.pRank q ↥(D ⊓ Subgroup.centralizer (Y : Set G)) ∧
        (z ∈ Subgroup.normalizer (Y : Set G) →
          D ⊓ Subgroup.centralizer (Y : Set G) =
            ⁅D ⊓ Subgroup.centralizer (Y : Set G), Subgroup.zpowers z⁆) ∧
        ∃ f ∈ F, B ≤ Subgroup.normalizer (conjugate Y f : Set G) ∧
          z ∈ Subgroup.normalizer (conjugate Y f : Set G)

@[expose] def CriticalOddCoreTwoActionRecognition : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p q : ℕ) (A R Q : Subgroup G), p.Prime → q.Prime →
    3 < p → q ≠ 2 → p ≠ q → Nat.card A = p → IsPGroup 2 R → A ≤ Subgroup.normalizer (R : Set G) →
    ⁅R, A⁆ = R → R ≠ ⊥ → Q.Normal → IsPGroup q Q → ⁅R, Q⁆ ≠ ⊥ →
    (∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(Q ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2) →
    p = 5 ∧ Nonempty (R ≃* QD32) ∧
      (∀ Y : Subgroup G, inSubgroup Subgroup.center R ≤ Y → Y ≤ R →
        A ≤ Subgroup.normalizer (Y : Set G) → Y = inSubgroup Subgroup.center R ∨ Y = R) ∧
      ∃ D : Subgroup G, D ≤ Q ∧ (D.subgroupOf Q).Characteristic ∧ D ≠ ⊥ ∧
        ⁅D, Q⁆ ≤ D ⊓ Subgroup.centralizer (D : Set G) ∧ (∀ d ∈ D, d ^ q = 1) ∧ ⁅D, R⁆ = D ∧
        R ⊓ Subgroup.centralizer (D : Set G) = ⊥ ∧ (inSubgroup frattini D).relIndex D = q ^ 4 ∧
        IsQDShape q D

@[expose] def ExtraspecialTwoActionOddCoreTorsionLifting : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (q : ℕ) (A R Q D : Subgroup G), q.Prime → q ≠ 2 → q ≠ 5 →
    Nat.card A = 5 → A ≤ Subgroup.normalizer (R : Set G) → ⁅R, A⁆ = R →
    Nonempty (R ≃* QD32) → Q.Normal → IsPGroup q Q → D ≤ Q → (D.subgroupOf Q).Characteristic →
    R ≤ Subgroup.normalizer (D : Set G) → R ⊓ Subgroup.centralizer (D : Set G) = ⊥ →
    IsQDShape q D →
    (∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(Q ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2) →
    omegaOne q Q = D

@[expose] def TwoLocalRankTwoOddCoreAction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p q : ℕ) (A R : Subgroup G), p.Prime → q.Prime → 3 < p →
    3 < q → p ≠ q → Nat.card A = p → A ≤ Subgroup.normalizer (R : Set G) → IsPGroup 2 R →
    R ≠ ⊥ → ⁅R, A⁆ = R → ⁅R, pCore q G⁆ ≠ ⊥ → localRank q G ≤ 2 →
    p = 5 ∧ Nonempty (R ≃* QD32) ∧ IsQDShape q (omegaOne q (pCore q G))

@[expose] def SmallOddCoreActionLiftingInsideLocalGroup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (q : ℕ), q.Prime → 5 < q → localRank q G ≤ 2 →
    ∀ H A R Q D : Subgroup G, A ≤ H → Nat.card A = 5 → R ≤ H →
    A ≤ Subgroup.normalizer (R : Set G) → IsPGroup 2 R → ⁅R, A⁆ = R → Nonempty (R ≃* QD32) →
    IsSylowOf q Q (((pCore q (↥H ⧸ pCore 2 ↥H)).comap (QuotientGroup.mk' (pCore 2 ↥H))).map
      H.subtype) →
    R ⊔ A ≤ Subgroup.normalizer (Q : Set G) → D ≤ Q → (D.subgroupOf Q).Characteristic →
    ⁅R, D⁆ ≠ ⊥ → IsQDShape q D →
    inSubgroup (pCore 2) H = ⊥ ∧ Q = inSubgroup (pCore q) H ∧
      D = omegaOne q (inSubgroup (pCore q) H)

end CFSG.RankThree.PartOne
