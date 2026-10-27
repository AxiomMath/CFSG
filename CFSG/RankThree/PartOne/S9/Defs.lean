module

public import CFSG.Foundations.SteinbergCAGeneratedCoreNodes
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.GroupTheory.SteinbergCETwoCoreAlpha
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

@[expose] def IsSylowOf {G : Type*} [Group G] (p : ℕ) (T K : Subgroup G) : Prop :=
  T ≤ K ∧ IsPGroup p T ∧ ¬ p ∣ T.relIndex K

@[expose] def omegaOne {G : Type*} [Group G] (q : ℕ) (K : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ K ∧ x ^ q = 1}

@[expose] def IsQDShape {G : Type*} [Group G] (q : ℕ) (D : Subgroup G) : Prop :=
  (IsElementaryAbelian q D ∧ Nat.card D = q ^ 4) ∨
    ((∀ x ∈ D, x ^ q = 1) ∧ Nat.card D = q ^ 5 ∧ Nat.card (⁅D, D⁆ : Subgroup G) = q ∧
      D ⊓ Subgroup.centralizer (D : Set G) = ⁅D, D⁆ ∧ inSubgroup frattini D = ⁅D, D⁆)

structure Sec9Hyp (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  kProper : KProper InCatalog G
  charTwo : IsCharTwoType G
  evenRank_eq : evenRank G = 3
  prime : p.Prime
  three_lt : 3 < p
  mem_sigma : p ∈ sigmaA G

@[expose] def GoodGlobalRank (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p = 7 → ∀ q ∈ sigmaA G, 7 < q → CFSG.pRank q G ≤ 3

@[expose] def LocalAlphaBound {G : Type*} [Group G] (p : ℕ) (A : Subgroup G) : Prop :=
  ∀ E : Subgroup G, E ≤ A → Nat.card E = p ^ 2 → ∀ c ∈ A, c ≠ 1 →
    (twoCoreAlpha (E.subgroupOf (Subgroup.centralizer ({c} : Set G)))).map
        (Subgroup.centralizer ({c} : Set G)).subtype ≤
      inSubgroup (pCore 2) (Subgroup.centralizer ({c} : Set G))

@[expose] noncomputable def residualGroup {G : Type*} [Group G] (p : ℕ) (K D : Subgroup G) (t : G) :
    Subgroup G :=
  ⁅inSubgroup (aschbacherSolvableCore p) (K ⊓ Subgroup.centralizer ({t} : Set G)), D⁆ ⊔
    ⨅ d ∈ D, ⨅ (_ : d ≠ 1),
      inSubgroup (aschbacherSolvableCore p) (K ⊓ Subgroup.centralizer ({d} : Set G))

structure MinTwoActionSetting {G : Type*} [Group G] (p q : ℕ) (A D R : Subgroup G) : Prop where
  prime_p : p.Prime
  prime_q : q.Prime
  three_lt_p : 3 < p
  q_ne_two : q ≠ 2
  p_ne_q : p ≠ q
  A_elem : IsElementaryAbelian p A
  A_card : Nat.card A = p ^ 2
  D_inv : R ⊔ A ≤ Subgroup.normalizer (D : Set G)
  D_pgroup : IsPGroup q D
  D_exp : ∀ x ∈ D, x ^ q = 1
  D_class : ⁅⁅D, D⁆, D⁆ = ⊥
  R_two : IsPGroup 2 R
  R_inv : A ≤ Subgroup.normalizer (R : Set G)
  R_comm : ⁅R, A⁆ = R
  R_ne : R ≠ ⊥
  R_act : ⁅R, D⁆ ≠ ⊥
  R_min : ∀ U : Subgroup G, U < R → A ≤ Subgroup.normalizer (U : Set G) → ⁅U, A⁆ = U →
    U ≤ Subgroup.centralizer (D : Set G)

@[expose] def IsFrattiniIrreducibleFor {G : Type*} [Group G] (L X : Subgroup G) : Prop :=
  L ≤ Subgroup.normalizer (X : Set G) ∧ inSubgroup frattini X < X ∧
    ∀ Y : Subgroup G, inSubgroup frattini X ≤ Y → Y ≤ X → L ≤ Subgroup.normalizer (Y : Set G) →
      Y = inSubgroup frattini X ∨ Y = X

theorem assembly_pRank_eq {G : Type*} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    (H : Subgroup G) : CFSG.Assembly.pRank q H = CFSG.pRank q H :=
  (CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hq H).symm

end CFSG.RankThree.PartOne
