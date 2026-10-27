module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofAsc93
public import CFSG.ClassicalInvolution.SmallCases.NobqOut
public import CFSG.RankThree.PartTwo.Sec3.Sims321Action
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartTwo.Sec18.Item185Count
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Basic

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartTwo.Sec19 (starIm IsList194 IsSmall194 IsTripleA6 IsProperParabolic
  Item194UsedWide3 Item316)

variable {G : Type} [Group G] [Finite G] {A M N L K : Subgroup G} {c : G}

@[expose] def planeGroup (A L : Subgroup G) (c : G) : Subgroup G :=
  L ⊓ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ⊓ Subgroup.centralizer ({c} : Set G)

@[expose] noncomputable def barActionImage (K B : Subgroup G) :
    Subgroup (MulAut (K ⧸ CFSG.pCore 2 K)) :=
  (B.subgroupOf (Subgroup.normalizer (K : Set G))).map (Sec3.Sims321.barAut K)

structure Facts1922 (G : Type) [Group G] [Finite G] (A M N L : Subgroup G) (c : G) : Prop where
  centralizer_eq : sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G)
  orderOf_c : orderOf c = 3
  normal : N ≤ Subgroup.normalizer (L : Set G)
  normalizer_eq : Subgroup.normalizer (L : Set G) = N
  eq_sup : A = Subgroup.zpowers c ⊔ (A ⊓ L)
  sylow : IsSylowOf 3 (A ⊓ L) L
  card : Nat.card (A ⊓ L : Subgroup G) = 9
  omega : ∀ Q : Subgroup G, IsSylowOf 3 Q N → A ≤ Q → Sec18.omegaOneThree Q = A
  sup_inf_eq : L ⊔ (N ⊓ M) = N
  not_le_M : ¬ L ≤ M
  pCoreOf_le_M : CFSG.Open.pCoreOf 2 L ≤ M
  normalizer_le_M : Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ≤ M

@[expose] def Item1922Facts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M N L : Subgroup G) (c : G), Hyp1921 G A M N L →
    sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G) →
    Facts1922 G A M N L c

@[expose] def InK194 (X : Type) [Group X] : Prop :=
  CFSG.IsQuasisimple X ∧ (IsList194 X ∨ IsSmall194 X ∨ IsTripleA6 X)

@[expose] def IsL3OddType (X : Type) [Group X] : Prop :=
  ∃ n : ℕ, Odd n ∧ Nonempty (X ≃* projSL 3 (GaloisField 2 n))

@[expose] def IsNoncyclicOutType (X : Type) [Group X] : Prop :=
  (∃ k : ℕ, 1 ≤ k ∧
    (Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 (2 * k))) ∨
      Nonempty (X ≃* projSL 3 (GaloisField 2 (2 * k))))) ∨
  Nonempty (X ≃* projSL 4 (GaloisField 2 2)) ∨ Nonempty (X ≃* alternatingGroup (Fin 6)) ∨
  IsTripleA6 X

@[expose] def ParabolicShape (X : Type) [Group X] (P : Subgroup X) : Prop :=
  (IsEmpty (X ≃* alternatingGroup (Fin 10)) ∧ IsProperParabolic P) ∨
    (Nonempty (X ≃* alternatingGroup (Fin 10)) ∧
      Sec4.IsExtOf P (Equiv.Perm (Fin 5)) (Multiplicative (Fin 4 → ZMod 2)))

@[expose] def OutTwoAbelian (X : Type) [Group X] : Prop :=
  ∀ P : Subgroup (Outer X), IsPGroup 2 P → ∀ x ∈ P, ∀ y ∈ P, x * y = y * x

@[expose] def OutTwoExpTwo (X : Type) [Group X] : Prop :=
  ∀ P : Subgroup (Outer X), IsPGroup 2 P → ∀ x ∈ P, x ^ 2 = 1

@[expose] def KF1 : Prop :=
  (∀ (X : Type) [Group X] [Finite X], InK194 X → OutTwoAbelian X) ∧
  (∀ (X : Type) [Group X] [Finite X], InK194 X →
    (IsL3OddType X ∨ IsTripleA6 X ∨
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))) → OutTwoExpTwo X) ∧
  (∀ (X : Type) [Group X] [Finite X], InK194 X → ¬ IsNoncyclicOutType X →
    CFSG.ClassicalInvolution.Nobq.OutTwoCyclic X)

@[expose] def KF2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], InK194 X → Nat.card (Subgroup.center X) ∣ 3 ∧
    (3 ∣ Nat.card (Subgroup.center X) →
      (∃ n : ℕ, Even n ∧ 1 ≤ n ∧
        Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n))) ∨ IsTripleA6 X)

@[expose] def KFBigPrime : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (k : ℕ), 2 ≤ k →
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 (2 * k))) →
      ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)

@[expose] def KF3a : Prop :=
  ∀ (X : Type) [Group X] [Finite X], InK194 X → ¬ IsL3OddType X →
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)

@[expose] def KF3b : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsL3OddType X →
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1 ∧ Subgroup.center X = ⊥

@[expose] def KF4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsL3OddType X → ∀ α : MulAut X, orderOf α = 3 →
    ∃ y : X, orderOf y = 3 ∧ α y = y

@[expose] def KF5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* projSL 3 (GaloisField 2 2)) →
    ∀ α : MulAut X, IsPGroup 3 (Subgroup.zpowers α) → α ^ 3 = 1

@[expose] def KF6 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* projSL 3 (GaloisField 2 2)) →
    ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
      ∀ H : Subgroup (MulAut X), (∀ α ∈ H, E.map α.toMonoidHom = E) → Group.IsSolvable ↥H

@[expose] def NoInvertingInParabolic (X : Type) [Group X] : Prop :=
  ∀ (P : Subgroup X) (D : Subgroup (MulAut X)), ParabolicShape X P →
    D ≤ P.map (MulAut.conj : X →* MulAut X) →
    CFSG.Assembly.IsElemAbelian 3 D → Nat.card D = 9 →
    D ≤ (Sec4.oTwoP 3 ↥(P.map (MulAut.conj : X →* MulAut X))).map
      (P.map (MulAut.conj : X →* MulAut X)).subtype →
    ∀ t ∈ P.map (MulAut.conj : X →* MulAut X), t ∈ Subgroup.normalizer (D : Set (MulAut X)) →
      ¬ ∀ d ∈ D, t * d * t⁻¹ = d⁻¹

@[expose] def NoSquareInvertingInParabolic (X : Type) [Group X] : Prop :=
  ∀ (P : Subgroup X) (D : Subgroup (MulAut X)), ParabolicShape X P →
    D ≤ P.map (MulAut.conj : X →* MulAut X) →
    CFSG.Assembly.IsElemAbelian 3 D → Nat.card D = 9 →
    D ≤ (Sec4.oTwoP 3 ↥(P.map (MulAut.conj : X →* MulAut X))).map
      (P.map (MulAut.conj : X →* MulAut X)).subtype →
    ∀ t ∈ P.map (MulAut.conj : X →* MulAut X), t ∈ Subgroup.normalizer (D : Set (MulAut X)) →
      ¬ ∀ d ∈ D, t ^ 2 * d * (t ^ 2)⁻¹ = d⁻¹

@[expose] def KFPar : Prop :=
  ∀ (X : Type) [Group X] [Finite X], InK194 X →
    (IsNoncyclicOutType X → NoInvertingInParabolic X) ∧
    (¬ IsNoncyclicOutType X → NoSquareInvertingInParabolic X)

@[expose] def KFL3Par : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), Odd n →
    Nonempty (X ≃* projSL 3 (GaloisField 2 n)) →
    (∀ P : Subgroup X, IsProperParabolic P → (∃ y ∈ P, orderOf y = 3) →
      Sec18.IsMaxParabolicRankTwo P ∧ P.index = (2 ^ n) ^ 2 + 2 ^ n + 1) ∧
    (∀ P Q R : Subgroup X, Sec18.IsMaxParabolicRankTwo P → Sec18.IsMaxParabolicRankTwo Q →
      Sec18.IsMaxParabolicRankTwo R →
      (∃ g : X, Q = P.map (MulAut.conj g).toMonoidHom) ∨
      (∃ g : X, R = P.map (MulAut.conj g).toMonoidHom) ∨
      (∃ g : X, R = Q.map (MulAut.conj g).toMonoidHom))

@[expose] def KFL3Two : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsL3OddType X → ∀ P : Subgroup X,
    Sec18.IsMaxParabolicRankTwo P → ∀ α : MulAut X, (∃ k : ℕ, α ^ 2 ^ k = 1) →
      (∃ g : X, P.map α.toMonoidHom = P.map (MulAut.conj g).toMonoidHom) → α ∈ inner X

@[expose] def KFL3Aut3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsL3OddType X → ∀ α : MulAut X, α ∉ inner X →
    α ^ 3 ∈ inner X → ∃ (t : X) (β : MulAut X), orderOf β = 3 ∧ α = MulAut.conj t * β

structure KFacts1923 : Prop where
  h194 : Item194UsedWide3
  h316 : Item316
  kf1 : KF1
  kf2 : KF2
  kfbig : KFBigPrime
  kf3a : KF3a
  kf3b : KF3b
  kf4 : KF4
  kf5 : KF5
  kf6 : KF6
  kfpar : KFPar
  kfl3par : KFL3Par
  kfl3two : KFL3Two
  kfl3aut3 : KFL3Aut3

theorem step1923_mem_oTwoComponentsIn (hK : K ∈ scriptJ M N) : K ∈ oTwoComponentsIn M := hK.1

theorem step1923_list (h194 : Item194UsedWide3) (h : Hyp1921 G A M N L) (hK : K ∈ scriptJ M N) :
    InK194 (K ⧸ CFSG.pCore 2 K) ∧ ParabolicShape (K ⧸ CFSG.pCore 2 K) (starIm K N) := by
  obtain ⟨-, hall⟩ := h194 G h.toSec19Std A M N h.isE27 h.mem_scriptM h.mem_scriptM_N h.ne
  obtain ⟨hlist, hpar⟩ := hall K hK
  exact ⟨⟨Sec18.isQuasisimple_of_mem_oTwoComponentsIn hK.1, hlist⟩, hpar⟩

theorem step1923_normalizer_A (h : Hyp1921 G A M N L) (hK : K ∈ oTwoComponentsIn M) :
    A ≤ Subgroup.normalizer (K : Set G) :=
  Sec18.Item185Proof.le_normalizer_of_ncard_le_two hK h.isE27.isPGroup h.le_M
    (Sec18.Item185Proof.ncard_conj_le_two h.toSec18Std hK)

end CFSG.RankThree.PartTwo.Late

namespace CFSG.RankThree.PartTwo

open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.Sec19 (starIm)

@[expose] def Item1923 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M N L : Subgroup G) (c : G),
    Late.Hyp1921 G A M N L →
    Late.sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G) →
    ∀ K ∈ Late.scriptJ M N,
      (∀ b ∈ A ⊓ L, ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) ∧
      Late.scriptJ M N = {K} ∧ CFSG.Open.pRank 3 K = 1 ∧
      (∃ n : ℕ, Odd n ∧ Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 n)) ∧
        ∃ ε : ℕ, (ε = 1 ∨ ε = 2) ∧
          (M ⊓ N).relIndex M = ((2 ^ n) ^ 2 + 2 ^ n + 1) * ε) ∧
      c ∈ K ∧ A ⊓ K = Subgroup.zpowers c ∧ M ≤ Subgroup.normalizer (K : Set G) ∧
        K = Late.normalClosureIn M c ∧
      Sec18.IsMaxParabolicRankTwo (starIm K N) ∧
        (∀ m ∈ M, (∀ k ∈ K, m * k * m⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M) → m ∈ N) ∧
      M ≤ Subgroup.normalizer (((A ⊓ L) ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) ∧
      (∀ P : Subgroup G, IsSylowOf 3 P (M ⊓ N) → A ≤ P →
        IsSylowOf 3 P M ∧ IsSylowOf 3 P N ∧ Sec18.omegaOneThree P = A ∧
        P = (P ⊓ K) ⊔ (A ⊓ L) ∧ Disjoint (P ⊓ K) (A ⊓ L) ∧
        (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧ IsCyclic ↥(P ⊓ K) ∧
        (∀ x ∈ P ⊓ K, x ^ 3 = 1 → x ∈ Subgroup.zpowers c) ∧
        ∃ C : Subgroup G, (C : Set G) = Late.sectionCentralizer M K (CFSG.Open.pCoreOf 2 M) ∧
          P ⊓ C = A ⊓ L ∧ IsSylowOf 3 (A ⊓ L) C ∧
          P ⊓ (K ⊔ C) = (P ⊓ K) ⊔ (A ⊓ L)) ∧
      ∀ P : Subgroup G, IsSylowOf 3 P M → c ∈ P →
        Sec18.conjugatesIn (Subgroup.zpowers c) P = {Subgroup.zpowers c}

end CFSG.RankThree.PartTwo
