module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49XA
public import CFSG.GroupTheory.ABGLocalTools.PStabilityChief
public import CFSG.Quasithin.Background.G6Natural

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def NatA5Sec (D N₀ N₁ : Subgroup G) : Prop :=
  ∃ (φ : ↥D →* alternatingGroup (Fin 5)) (ψ : ↥N₀ →* ↥(CFSG.Quasithin.G6.coreMod 5)),
    Function.Surjective φ ∧ Function.Surjective ψ ∧ ψ.ker = N₁.subgroupOf N₀ ∧
    ∀ (d : ↥D) (n n' : ↥N₀), (n' : G) = (d : G) * n * (d : G)⁻¹ →
      ψ n' = CFSG.Quasithin.G6.coreAct 5 (φ d : Equiv.Perm (Fin 5)) (ψ n)

abbrev HChief (H N M : Subgroup G) : Prop := CFSG.ABGLocalTools.IsChiefFactorUnder 2 H N M

@[expose] noncomputable def wIdx (Z N M : Subgroup G) : ℕ :=
  ((N ⊓ Subgroup.centralizer (Z : Set G)) ⊔ M).relIndex N

structure XAData (X L I : Subgroup G) (x : G) (A : Subgroup G) (a n : G) : Prop where
  A_le : A ≤ I
  reg : XReg49 X A
  A3 : IsPGroup 3 A
  idx : ¬ 3 ∣ (A.subgroupOf I).index
  a_mem : a ∈ L
  ord : orderOf a = 3
  gen : A = Subgroup.closure {a, cj x a, cj (x ^ 2) a}
  n_mem : n ∈ I
  inv_a : cj n a = a⁻¹
  fix_b : cj n (cj x a) = cj x a
  fix_c : cj n (cj (x ^ 2) a) = cj (x ^ 2) a

theorem xaData_exists {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hx : X = Subgroup.zpowers x) : ∃ (A : Subgroup G) (a n : G), XAData X L I x A a n := by
  obtain ⟨A, a, n, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := xa49 h hx
  exact ⟨A, a, n, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩⟩

@[expose] def FiveRankBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N M B : Subgroup G) (k : ℕ),
    M ≤ N → (∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ∈ M) → (∀ x ∈ N, x ^ 2 ∈ M) →
    CFSG.Open.IsElemAbelian 5 B → Nat.card B = 5 ^ k →
    B ≤ Subgroup.normalizer (N : Set G) → B ≤ Subgroup.normalizer (M : Set G) →
    (∀ b ∈ B, (∀ n ∈ N, ⁅n, b⁆ ∈ M) → b = 1) →
    2 ^ (4 * k) ≤ M.relIndex N

@[expose] def Q8D8Counts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G),
    CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 N → Nat.card {n : N // n * n = 1} = 12

@[expose] def A5MinusModule : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D N₀ N₁ : Subgroup G),
    N₁ ≤ N₀ → IsPGroup 2 N₀ →
    D ≤ Subgroup.normalizer (N₀ : Set G) → D ≤ Subgroup.normalizer (N₁ : Set G) →
    (∀ x ∈ N₀, ∀ y ∈ N₀, ⁅x, y⁆ ∈ N₁) → (∀ x ∈ N₀, x ^ 2 ∈ N₁) →
    N₁.relIndex N₀ = 16 →
    (∀ Y : Subgroup G, N₁ ≤ Y → Y ≤ N₀ → D ≤ Subgroup.normalizer (Y : Set G) →
      Y = N₁ ∨ Y = N₀) →
    (∃ φ : ↥D →* alternatingGroup (Fin 5), Function.Surjective φ ∧
      ∀ d : ↥D, φ d = 1 ↔ ∀ n ∈ N₀, ⁅n, (d : G)⁆ ∈ N₁) →
    (∃ d ∈ D, orderOf d = 3 ∧
      ((N₀ ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ N₁).relIndex N₀ = 4) →
    NatA5Sec D N₀ N₁

@[expose] def Inputs49 : Prop := FiveRankBound ∧ Q8D8Counts ∧ A5MinusModule

@[expose] def ChiefShape49 (H L Q : Subgroup G) (x : G) (N M : Subgroup G) : Prop :=
  ∀ V : ℕ → Subgroup G, (∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M) →
    N = V 0 ⊔ V 1 ⊔ V 2 ∧
    (V 0 ⊓ (V 1 ⊔ V 2) = M ∧ V 1 ⊓ (V 0 ⊔ V 2) = M ∧ V 2 ⊓ (V 0 ⊔ V 1) = M) ∧
    (∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → ⁅V i, Lc L x j⁆ ≤ M) ∧
    (∀ i : ℕ, i < 3 → HChief (Lc L x i ⊔ Q) (V i) M)

@[expose] def Part1_49 (X L : Subgroup G) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, CFSG.conjugate L x ≠ CFSG.conjugate L y →
    ⁅CFSG.conjugate L x, CFSG.conjugate L y⁆ = ⊥

@[expose] def Part2_49 (Q I : Subgroup G) : Prop :=
  Q = (Q ⊓ Subgroup.centralizer (I : Set G)) ⊔ ⁅Q, I⁆ ∧
    ⁅Q ⊓ Subgroup.centralizer (I : Set G), ⁅Q, I⁆⁆ = ⊥

@[expose] def Part3_49 (H Q I : Subgroup G) : Prop :=
  (IsMulCommutative ↥(Q ⊓ Subgroup.centralizer (I : Set G)) ∨
      CFSG.Open.pRank 2 (Q ⊓ Subgroup.centralizer (I : Set G)) = 1) →
    CFSG.Open.IsElemAbelian 2
      (CFSG.RankThree.PartOne.omegaOne 2 (Q ⊓ Subgroup.centralizer (I : Set G))) ∧
    H ≤ Subgroup.normalizer
      (CFSG.RankThree.PartOne.omegaOne 2 (Q ⊓ Subgroup.centralizer (I : Set G)) : Set G) ∧
    ∀ (p : ℕ), p.Prime → ∀ E : Subgroup G, E ≤ H → H ≤ Subgroup.normalizer (E : Set G) →
      CFSG.Open.IsElemAbelian p E →
      E ≤ CFSG.RankThree.PartOne.omegaOne 2 (Q ⊓ Subgroup.centralizer (I : Set G))

theorem concl49_iff {H X L Q I : Subgroup G} :
    Concl49 H X L Q I ↔ Part1_49 X L ∧ Part2_49 Q I ∧ Part3_49 H Q I := Iff.rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
