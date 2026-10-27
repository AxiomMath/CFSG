module

public import CFSG.RankThree.PartOne.S9.Defs
public import CFSG.Foundations.Catalog
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open scoped commutatorElement Pointwise

@[expose] def SectionEightResidualBound : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsKGroup X → evenRank X ≤ 3 →
    ∀ p : ℕ, p.Prime → 3 < p → ∀ E : Subgroup X, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 →
      (((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set X)), E⁆ ⊔
          thetaT p E : Subgroup X) : Set X) =
        ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set X)), E⁆ :
          Subgroup X) : Set X) * (thetaT p E : Set X)) ∧
      CFSG.Quasithin.twoPrimeResidual
          (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set X)), E⁆ ⊔
            thetaT p E) ≤ aschbacherSolvableCore p X

@[expose] def ProperSubgroupResidual : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → evenRank G ≤ 3 →
    ∀ p : ℕ, p.Prime → 3 < p → ∀ B : Subgroup G, IsElementaryAbelian p B →
    Nat.card B = p ^ 2 → ∀ K : Subgroup G, B ≤ K → K ≠ ⊤ → ∀ b ∈ B, b ≠ 1 →
      CFSG.Quasithin.twoPrimeResidual (residualGroup p K B b) ≤
        inSubgroup (aschbacherSolvableCore p) K

@[expose] def ResidualTwoSubgroupTransfer : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Subgroup.center G = ⊥ → KProper InCatalog G →
    evenRank G ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p → ∀ A : Subgroup G, IsElementaryAbelian p A →
    Nat.card A = p ^ 3 → ∀ c ∈ A, c ≠ 1 → ∀ R : Subgroup G,
    R ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) →
    IsPGroup 2 R → A ≤ Subgroup.normalizer (R : Set G) → ⁅R, A⁆ = R →
    Nat.card (A ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) = p ^ 2 →
    c ∈ Subgroup.centralizer (R : Set G) →
    (∀ b ∈ A ⊓ Subgroup.centralizer (R : Set G), b ≠ 1 →
      R ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G))) ∧
    ∀ M : Subgroup G, A ⊓ Subgroup.centralizer (R : Set G) ≤ M → M ≠ ⊤ →
      R ⊓ M ≤ inSubgroup (aschbacherSolvableCore p) M

@[expose] def InitialCriticalAction : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ), p.Prime → p ≠ 2 → ∀ A T : Subgroup H,
    IsElementaryAbelian p A → Nat.card A = p ^ 3 → IsSylowOf 2 T (aschbacherSolvableCore p H) →
    A ≤ Subgroup.normalizer (T : Set H) → ¬ ⁅T, A⁆ ≤ pCore 2 H →
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ p ∧ ∃ R Q D : Subgroup H, R ≤ T ∧
      A ≤ Subgroup.normalizer (R : Set H) ∧ ⁅R, A⁆ = R ∧ ¬ R ≤ pCore 2 H ∧
      (∀ U : Subgroup H, U < R → A ≤ Subgroup.normalizer (U : Set H) → ⁅U, A⁆ = U →
        U ≤ pCore 2 H ∧ U ≤ Subgroup.centralizer (D : Set H)) ∧
      IsSylowOf q Q ((pCore q (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H))) ∧
      R ≤ Subgroup.normalizer (Q : Set H) ∧ A ≤ Subgroup.normalizer (Q : Set H) ∧
      D ≤ Q ∧ (D.subgroupOf Q).Characteristic ∧ D ≠ ⊥ ∧ ⁅R, D⁆ ≠ ⊥ ∧ (∀ d ∈ D, d ^ q = 1) ∧
      ⁅D, Q⁆ ≤ D ⊓ Subgroup.centralizer (D : Set H) ∧
      Nat.card (A ⊓ Subgroup.centralizer (R : Set H) : Subgroup H) = p ^ 2 ∧
      ∀ C : Subgroup H, C ≤ A → C.Normal → C ≤ A ⊓ Subgroup.centralizer (R : Set H)

@[expose] def CentralizerConstrainedCriticalAction : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ), p.Prime → p ≠ 2 → ∀ A : Subgroup H,
    IsElementaryAbelian p A → Nat.card A = p ^ 3 → ∀ b ∈ A, b ≠ 1 →
    ⁅inSubgroup (pCore 2) (Subgroup.centralizer ({b} : Set H)), A⁆ ≤
      aschbacherSolvableCore p H →
    ¬ ⁅inSubgroup (pCore 2) (Subgroup.centralizer ({b} : Set H)), A⁆ ≤ pCore 2 H →
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ p ∧ ∃ R Q D : Subgroup H,
      R ≤ inSubgroup (pCore 2) (Subgroup.centralizer ({b} : Set H)) ⊓
        aschbacherSolvableCore p H ∧
      A ≤ Subgroup.normalizer (R : Set H) ∧ ⁅R, A⁆ = R ∧ ¬ R ≤ pCore 2 H ∧
      (∀ U : Subgroup H, U < R → A ≤ Subgroup.normalizer (U : Set H) → ⁅U, A⁆ = U →
        U ≤ pCore 2 H ∧ U ≤ Subgroup.centralizer (D : Set H)) ∧
      IsSylowOf q Q ((pCore q (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H))) ∧
      R ≤ Subgroup.normalizer (Q : Set H) ∧ A ≤ Subgroup.normalizer (Q : Set H) ∧
      D ≤ Q ∧ (D.subgroupOf Q).Characteristic ∧ D ≠ ⊥ ∧ ⁅R, D⁆ ≠ ⊥ ∧ (∀ d ∈ D, d ^ q = 1) ∧
      ⁅D, Q⁆ ≤ D ⊓ Subgroup.centralizer (D : Set H) ∧
      Nat.card (A ⊓ Subgroup.centralizer (R : Set H) : Subgroup H) = p ^ 2 ∧
      b ∈ Subgroup.centralizer (R : Set H) ∧
      ∀ C : Subgroup H, C ≤ A → C.Normal → C ≤ A ⊓ Subgroup.centralizer (R : Set H)

@[expose] def SylowTwoAlternatives : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), Sec9Hyp G p →
    ∀ A : Subgroup G, IsElementaryAbelian p A → Nat.card A = p ^ 3 → ∀ c ∈ A, c ≠ 1 →
    ∀ T : Subgroup G,
      IsSylowOf 2 T (inSubgroup (aschbacherSolvableCore p)
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))) →
      A ≤ Subgroup.normalizer (T : Set G) →
      ⁅T, A⁆ ≤ inSubgroup (pCore 2) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∨
      (p ≤ 7 ∧
        (∀ b ∈ A, b ≠ 1 →
          ⁅inSubgroup (pCore 2) (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
              Subgroup.centralizer ({b} : Set G)), A⁆ ≤
            inSubgroup (pCore 2) (Subgroup.normalizer (Subgroup.zpowers c : Set G))) ∧
        ∃ a ∈ A, a ≠ 1 ∧
          ⁅inSubgroup (pCore 2) (Subgroup.centralizer ({a} : Set G)), A⁆ ≠ ⊥) ∨
      (p = 7 ∧ ∃ q ∈ sigmaA G, 7 < q ∧ 3 < CFSG.pRank q G)

@[expose] def TrivialGlobalTwoCoreAction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), Sec9Hyp G p → GoodGlobalRank G p →
    ∀ A : Subgroup G, IsElementaryAbelian p A → Nat.card A = p ^ 3 →
    (∀ a ∈ A, a ≠ 1 → ⁅inSubgroup (pCore 2) (Subgroup.centralizer ({a} : Set G)), A⁆ = ⊥) →
    ∀ c ∈ A, c ≠ 1 → ∀ T : Subgroup G,
      IsSylowOf 2 T (inSubgroup (aschbacherSolvableCore p)
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))) →
      A ≤ Subgroup.normalizer (T : Set G) → ⁅T, A⁆ = ⊥

@[expose] def CentralizerTwoCoreCommutatorBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), Sec9Hyp G p → GoodGlobalRank G p →
    ∀ A : Subgroup G, IsElementaryAbelian p A → Nat.card A = p ^ 3 → ∀ c ∈ A, c ≠ 1 →
    ∀ b ∈ A, b ≠ 1 →
      ⁅inSubgroup (pCore 2) (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
          Subgroup.centralizer ({b} : Set G)), A⁆ ≤
        inSubgroup (pCore 2) (Subgroup.normalizer (Subgroup.zpowers c : Set G))

@[expose] def NormalOddCoreActionKernelCentralization : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), Sec9Hyp G p → GoodGlobalRank G p →
    ∀ A R : Subgroup G, IsElementaryAbelian p A → Nat.card A = p ^ 3 → IsPGroup 2 R →
    A ≤ Subgroup.normalizer (R : Set G) → ⁅R, A⁆ = R → R ≠ ⊥ →
    Nat.card (A ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) = p ^ 2 →
    ∀ b ∈ A ⊓ Subgroup.centralizer (R : Set G), b ≠ 1 →
    R ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.normalizer (Subgroup.zpowers b : Set G)) →
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → ∀ X : Subgroup G,
    X ≤ inSubgroup (pCore q) (Subgroup.normalizer (Subgroup.zpowers b : Set G)) →
    R ⊔ A ≤ Subgroup.normalizer (X : Set G) → (∀ x ∈ X, x ^ q = 1) → ⁅⁅X, X⁆, X⁆ = ⊥ →
    ⁅R, X⁆ ≠ ⊥ →
    (∀ U : Subgroup G, U < R → A ≤ Subgroup.normalizer (U : Set G) → ⁅U, A⁆ = U →
      U ≤ Subgroup.centralizer (X : Set G)) →
    ⁅A ⊓ Subgroup.centralizer (R : Set G), X⁆ = ⊥

@[expose] def ExceptionalSmallActionExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → IsCharTwoType G → evenRank G ≤ 3 →
    ∀ q : ℕ, q.Prime → 5 < q → localRank q G ≤ 2 → ∀ A R D : Subgroup G, ∀ c ∈ A, c ≠ 1 →
      ¬ (IsElementaryAbelian 5 A ∧ Nat.card A = 125 ∧
        R ≤ inSubgroup (aschbacherSolvableCore 5)
          (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∧
        A ≤ Subgroup.normalizer (R : Set G) ∧ ⁅R, A⁆ = R ∧ Nonempty (R ≃* QD32) ∧
        Nat.card (A ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) = 25 ∧
        c ∈ Subgroup.centralizer (R : Set G) ∧
        D = omegaOne q (inSubgroup (pCore q) (Subgroup.normalizer (Subgroup.zpowers c : Set G))) ∧
        R ⊓ Subgroup.centralizer (D : Set G) = ⊥ ∧ IsQDShape q D)

@[expose] def AlphaZeroSylowCentralization : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), Sec9Hyp G p → GoodGlobalRank G p →
    ∀ A : Subgroup G, IsElementaryAbelian p A → Nat.card A = p ^ 3 →
    ∀ B : Subgroup G, B ≤ A → Nat.card B = p ^ 2 → twoCoreAlpha B = ⊥ →
    (∀ a ∈ A, a ≠ 1 → ⁅inSubgroup (pCore 2) (Subgroup.centralizer ({a} : Set G)), A⁆ = ⊥) ∧
    ∀ c ∈ A, c ≠ 1 → ∃ T : Subgroup G,
      IsSylowOf 2 T (inSubgroup (aschbacherSolvableCore p)
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))) ∧ ⁅T, A⁆ = ⊥

@[expose] def AlphaZeroOddIntersection : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), Sec9Hyp G p → GoodGlobalRank G p →
    ∀ A : Subgroup G, IsElementaryAbelian p A → Nat.card A = p ^ 3 →
    ∀ B : Subgroup G, B ≤ A → Nat.card B = p ^ 2 → twoCoreAlpha B = ⊥ →
    Odd (Nat.card (thetaT p B))

@[expose] def CoreVanishingDichotomy : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), Sec9Hyp G p → GoodGlobalRank G p →
    ∀ A : Subgroup G, IsElementaryAbelian p A → Nat.card A = p ^ 3 → ∀ P : Sylow p G,
    A ≤ (P : Subgroup G) → ∀ B : Subgroup G, B ≤ A → Nat.card B = p ^ 2 → ∀ c ∈ A, c ≠ 1 →
      (twoCoreAlpha B ≠ ⊥ ∧ ∃ H₀ : Subgroup G, IsTwoLocal H₀ ∧ aschCore 2 p (P : Subgroup G) ≤ H₀) ∨
      (twoCoreAlpha B = ⊥ ∧ (∃ T : Subgroup G,
        IsSylowOf 2 T (inSubgroup (aschbacherSolvableCore p)
          (Subgroup.normalizer (Subgroup.zpowers c : Set G))) ∧ ⁅T, A⁆ = ⊥) ∧
        Odd (Nat.card (thetaT p B)))

end CFSG.RankThree.PartOne
