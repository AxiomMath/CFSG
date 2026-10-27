module

public import CFSG.Quasithin.Vol2.Ch3Sec1Defs
public import CFSG.Quasithin.Background.E2TwoLieQuot
public import CFSG.Quasithin.Background.F8Basic
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.Quasithin.Background.BlueprintB2Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

section Vocabulary

variable {G : Type} [Group G]

abbrev O2Q (X : Subgroup G) : Type := ↥X ⧸ CFSG.pCore 2 ↥X

@[expose] def IsCh5Module (T L V : Subgroup G) : Prop :=
  V ≤ L ⊔ T ∧ IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)) ∧ ⁅V, L⁆ ≠ ⊥

@[expose] def IsNatModCh5 (L W : Subgroup G) (n : ℕ) : Prop :=
  L ≤ Subgroup.normalizer (W : Set G) ∧
    ∃ _ : IsMulCommutative ↥W, BinaryNaturalSL (V := ↥W) (autOn L W) ⊤ ⊥ 2 n

@[expose] def IsNatQuotCh5 (L W : Subgroup G) (n : ℕ) : Prop :=
  L ≤ Subgroup.normalizer (W : Set G) ∧
    ∃ _ : IsMulCommutative ↥W, BinaryNaturalSL (V := ↥W) (autOn L W) ⊤
      ((Subgroup.centralizer (L : Set G)).subgroupOf W) 2 n

@[expose] def IsBarS5 (L T V : Subgroup G) : Prop :=
  Nonempty (↥(autOn (L ⊔ T) V) ≃* Equiv.Perm (Fin 5))

@[expose] def IsS5ModCh5 (L T W : Subgroup G) : Prop :=
  L ⊔ T ≤ Subgroup.normalizer (W : Set G) ∧
    ∃ _ : IsMulCommutative ↥W, SymmetricNatural (V := ↥W) (autOn (L ⊔ T) W) ⊤ ⊥ 5

@[expose] def IsOrthCh5 (L V : Subgroup G) (n : ℕ) : Prop :=
  ∃ m : ℕ, n = 2 * m ∧ L ≤ Subgroup.normalizer (V : Set G) ∧
    ∃ _ : IsMulCommutative ↥V, BinaryOrthogonalFour (V := ↥V) (autOn L V) ⊤ ⊥ m

@[expose] def IsSumOfTwo (X W : Subgroup G) (P : Subgroup G → Prop) : Prop :=
  ∃ W₁ W₂ : Subgroup G, X ≤ Subgroup.normalizer (W₁ : Set G) ∧
    X ≤ Subgroup.normalizer (W₂ : Set G) ∧ W₁ ⊓ W₂ = ⊥ ∧ W₁ ⊔ W₂ = W ∧ P W₁ ∧ P W₂

@[expose] def IsCommCentralSplit (L T V : Subgroup G) : Prop :=
  ⁅V, L⁆ ⊓ (V ⊓ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G)) = ⊥ ∧
    ⁅V, L⁆ ⊔ V ⊓ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G) = V

abbrev borelL (T L : Subgroup G) : Subgroup G :=
  L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)

@[expose] def IsBenderCh5 (k : ℕ) (X : Type) [Group X] : Prop :=
  LieModel X .PSL 2 2 k ∨ SuzukiModel X 2 k ∨
    (CFSG.IsQuasisimple X ∧ LieModel (X ⧸ Subgroup.center X) .PSU 3 2 k)

@[expose] def IsSL3Ch5 (k : ℕ) (X : Type) [Group X] : Prop :=
  LieModel X .PSL 3 2 k ∨
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) F)

@[expose] def IsRankOneParabolicOver (K S₀ P : Subgroup G) : Prop :=
  K ⊓ Subgroup.normalizer (S₀ : Set G) < P ∧ P ≤ K ∧
    ∀ Q : Subgroup G, K ⊓ Subgroup.normalizer (S₀ : Set G) < Q → Q ≤ P → Q = P

@[expose] def IsMaxParabolicOver (K S₀ P : Subgroup G) : Prop :=
  P ≤ K ∧ K ⊓ Subgroup.normalizer (S₀ : Set G) ≤ P ∧ P ≠ K ∧
    ∀ Q : Subgroup G, P ≤ Q → Q ≤ K → Q ≠ K → Q = P

abbrev centralizerModO2 (K : Subgroup G) : Subgroup G :=
  centralizerMod (pCoreOf 2 K) (Subgroup.normalizer (K : Set G)) K

end Vocabulary

structure Hyp5_0_1 (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : QuasithinUnique.quasithinIsQTKECat G
  sylow : quasithinIsSylowTwo T
  maxTwoLocal : quasithinIsMaxTwoLocal M
  T_le : T ≤ M
  maximal : quasithinIsMaximalLocal T L
  faithful : quasithinIsFaithfulLocal T L
  L_le : L ≤ M
  normal : M ≤ Subgroup.normalizer (L : Set G)
  two_le : 2 ≤ n
  lie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n

@[expose] def Stmt5_1_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp5_0_1 G T M L n →
    IsCh5Module T L V →
      T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) ∧
      (∀ H : Subgroup G, IsHStar T M H →
        MinParabolic H T (H ⊓ M) ∧ (1 < E1.nParam H → ¬ Group.IsSolvable ↥H ∧ SQTKGroup ↥H)) ∧
      (∀ H : Subgroup G, IsHStar T M H →
        Hyp315Base T M (L ⊔ T) H V ∧ Hyp315.CaseI M (L ⊔ T) H) ∧
      ∃ N : Subgroup G, MinParabolic (L ⊔ T) T N

@[expose] def Stmt5_1_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp5_0_1 G T M L n →
    IsCh5Module T L V →
      (thompsonJ T ≤ M ⊓ Subgroup.centralizer (V : Set G) ∧
          L ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G) ∧
          L ⊔ T ≤ Subgroup.normalizer (baum T : Set G) ∧
          IsUniqueM (Subgroup.normalizer (thompsonJ T : Set G)) M ∧
          IsUniqueM (Subgroup.normalizer (baum T : Set G)) M) ∨
      (⁅V, thompsonJ T⁆ ≠ ⊥ ∧ IsNatQuotCh5 L V n) ∨
      (⁅V, thompsonJ T⁆ ≠ ⊥ ∧ n = 2 ∧ IsCommCentralSplit L T V ∧ IsBarS5 L T V ∧
        IsS5ModCh5 L T ⁅V, L⁆)

@[expose] def Stmt5_1_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp5_0_1 G T M L n →
    IsCh5Module T L V →
      IsSumOfTwo L V (fun W => IsNatModCh5 L W n) ∨
      (n = 2 ∧ IsBarS5 L T V ∧ IsSumOfTwo (L ⊔ T) V (IsS5ModCh5 L T)) ∨
      IsNatQuotCh5 L ⁅V, L⁆ n ∨
      IsOrthCh5 L V n ∨
      (IsCommCentralSplit L T V ∧ IsBarS5 L T V ∧ IsS5ModCh5 L T ⁅V, L⁆)

@[expose] def Stmt5_1_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L H D : Subgroup G) (n : ℕ), Hyp5_0_1 G T M L n →
    IsHStar T M H → Lin2.IsHallTwoPrimeOf D (borelL T L) →
      H ⊓ M ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ∧
      H ⊓ M ≤ Subgroup.normalizer (oTwoUpper (D ⊔ T) : Set G) ∧
      ((∃ K ∈ cComp H, E2.HasE22LieQuot K) → Group.IsSolvable ↥(H ⊓ M) ∧
        ∃ B : Subgroup G, Lin2.IsHallTwoPrimeOf B (H ⊓ M) ∧
          B ≤ Subgroup.normalizer (D : Set G))

@[expose] def Stmt5_1_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H D : Subgroup G) (n : ℕ), Hyp5_0_1 G T M L n →
    IsCh5Module T L V → IsHStar T M H → Lin2.IsHallTwoPrimeOf D (borelL T L) →
    pCoreOf 2 (D ⊔ H) = ⊥ →
      Even n ∧
      ((n = 2 ∧ IsSumOfTwo L V (fun W => IsNatModCh5 L W n) ∧
          ⁅quasithinOmegaOneCenter T, H⁆ = ⊥) ∨
        ((n = 2 ∨ n = 4) ∧ IsNatModCh5 L ⁅V, L⁆ n ∧ ⁅quasithinOmegaOneCenter T, H⁆ = ⊥) ∨
        (n = 2 ∧ IsBarS5 L T V ∧ IsS5ModCh5 L T ⁅V, L⁆ ∧ centerOf H = ⊥) ∨
        (n % 4 = 0 ∧ IsOrthCh5 L V n ∧ ⁅quasithinOmegaOneCenter T, H⁆ = ⊥ ∧
          ∀ Dp Dm : Subgroup G, Dp ≤ D → Dm ≤ D → Nat.card Dp = 2 ^ (n / 2) - 1 →
            Nat.card Dm = 2 ^ (n / 2) + 1 →
              quasithinOmegaOneCenter T ≤ centerOf (Dm ⊔ H) ∧
                (pCoreOf 2 (Dp ⊔ H) ≠ ⊥ ∨ n = 4 ∨ n = 8)))

@[expose] def Stmt5_1_7_two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H : Subgroup G) (n : ℕ), Hyp5_0_1 G T M L n →
    IsCh5Module T L V → IsHStar T M H → ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ →
      L = ⁅L, thompsonJ T⁆ ∧ oTwoUpper H = ⁅oTwoUpper H, thompsonJ T⁆ ∧
      (pCoreOf 2 (borelL T L ⊔ H) ≠ ⊥ ∨
        (IsBarS5 L T V ∧ IsS5ModCh5 L T ⁅V, L⁆ ∧ centerOf H = ⊥))

structure Hyp5_1_8 (G : Type) [Group G] [Finite G] (T M L H : Subgroup G) (n : ℕ) : Prop
    extends Hyp5_0_1 G T M L n where
  hStar : IsHStar T M H
  lieQuot : ∃ K ∈ cComp H, E2.HasE22LieQuot K

section Notation59

variable {G : Type} [Group G]

@[expose] def IsNotation5_1_9 (T M L H B D : Subgroup G) : Prop :=
  Lin2.IsHallTwoPrimeOf B (M ⊓ H) ∧ Lin2.IsHallTwoPrimeOf D (borelL T L) ∧
    B ≤ Subgroup.normalizer (D : Set G)

end Notation59

@[expose] def Stmt5_1_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L H B D : Subgroup G) (n : ℕ), Hyp5_1_8 G T M L H n →
    IsNotation5_1_9 T M L H B D →
      ∃ k : ℕ, (2 ≤ k ∧ E1.nParam H ≤ k) ∧
        E2.IsBorelIn (oTwoUpper H) (M ⊓ oTwoUpper H) ∧
        Lin2.IsHallTwoPrimeOf B (M ⊓ oTwoUpper H) ∧
        ∃ K₁ : Subgroup G, quasithinIsCComponent K₁ H ∧ oTwoUpper H = conjClosure K₁ T ∧
          ((K₁ < oTwoUpper H ∧ (LieModel (O2Q K₁) .PSL 2 2 k ∨ SuzukiModel (O2Q K₁) 2 k)) ∨
            (K₁ = oTwoUpper H ∧ IsBenderCh5 k (O2Q (oTwoUpper H))) ∨
            (K₁ = oTwoUpper H ∧
              (IsSL3Ch5 k (O2Q (oTwoUpper H)) ∨ LieModel (O2Q (oTwoUpper H)) .PSp 2 2 k) ∧
              E2.IsDiagramNontrivial T (oTwoUpper H) (T ⊓ oTwoUpper H)))

@[expose] def IsFieldParam510 {G : Type} [Group G] (T H : Subgroup G) (k : ℕ) : Prop :=
  (2 ≤ k ∧ E1.nParam H ≤ k) ∧
    ∃ K₁ : Subgroup G, quasithinIsCComponent K₁ H ∧ oTwoUpper H = conjClosure K₁ T ∧
      ((K₁ < oTwoUpper H ∧ (LieModel (O2Q K₁) .PSL 2 2 k ∨ SuzukiModel (O2Q K₁) 2 k)) ∨
        (K₁ = oTwoUpper H ∧ IsBenderCh5 k (O2Q (oTwoUpper H))) ∨
        (K₁ = oTwoUpper H ∧
          (IsSL3Ch5 k (O2Q (oTwoUpper H)) ∨ LieModel (O2Q (oTwoUpper H)) .PSp 2 2 k) ∧
          E2.IsDiagramNontrivial T (oTwoUpper H) (T ⊓ oTwoUpper H)))

theorem Stmt5_1_10.exists_fieldParam (h510 : Stmt5_1_10) {G : Type} [Group G] [Finite G]
    {T M L H B D : Subgroup G} {n : ℕ} (hyp : Hyp5_1_8 G T M L H n)
    (hN : IsNotation5_1_9 T M L H B D) : ∃ k : ℕ, IsFieldParam510 T H k := by
  obtain ⟨k, hk, -, -, K₁, hK₁, hKeq, hc⟩ := h510 G T M L H B D n hyp hN
  exact ⟨k, hk, K₁, hK₁, hKeq, hc⟩

@[expose] def IsLieRankTwoK {G : Type} [Group G] (T H : Subgroup G) : Prop :=
  (∃ K₁ : Subgroup G, quasithinIsCComponent K₁ H ∧ oTwoUpper H = conjClosure K₁ T ∧
      K₁ < oTwoUpper H) ∨
    ∃ k : ℕ, IsSL3Ch5 k (O2Q (oTwoUpper H)) ∨ LieModel (O2Q (oTwoUpper H)) .PSp 2 2 k

@[expose] def Stmt5_1_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L H B D : Subgroup G) (n : ℕ), Hyp5_1_8 G T M L H n →
    IsNotation5_1_9 T M L H B D →
      IsSylowTwoOf (pCoreOf 2 (M ⊓ H) ⊓ oTwoUpper H) (oTwoUpper H) ∧
      IsSylowTwoOf (pCoreOf 2 (M ⊓ H) ⊓ L) L ∧
      (IsLieRankTwoK T H →
        (∀ P : Subgroup G, IsRankOneParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P →
            pCoreOf 2 (M ⊓ H) ≤ Subgroup.normalizer (P : Set G)) ∨
          (LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 ∧
            (oTwoUpper H ⊔ pCoreOf 2 H).relIndex (oTwoUpper H ⊔ pCoreOf 2 (M ⊓ H)) = 2 ∧
            E2.IsDiagramNontrivial (pCoreOf 2 (M ⊓ H)) (oTwoUpper H) (T ⊓ oTwoUpper H)))

@[expose] def Concl5_1_14 {G : Type} [Group G] [Finite G] (T L V H B D : Subgroup G) (n : ℕ) :
    Prop :=
  (quasithinIsMaximalLocal T (oTwoUpper H) ∧
      IsUniqueM H (Subgroup.normalizer (oTwoUpper H : Set G)) ∧
      ¬ quasithinIsFaithfulLocal T (oTwoUpper H)) ∧
    (⁅quasithinOmegaOneCenter T, H⁆ = ⊥ ∧
      ∀ z ∈ quasithinOmegaOneCenter T, z ≠ 1 →
        Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (oTwoUpper H : Set G)) ∧
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
    (n = 2 ∧
      ((IsBarS5 L T V ∧ (IsS5ModCh5 L T V ∨ IsSumOfTwo (L ⊔ T) V (IsS5ModCh5 L T))) ∨
        IsOrthCh5 L V 2) ∧
      D = B) ∧
    (Group.IsSolvable ↥(centralizerModO2 (oTwoUpper H)) ∧
      ¬ 3 ∣ Nat.card ↥(centralizerModO2 (oTwoUpper H)))

@[expose] def Stmt5_1_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → Concl5_1_14 T L V H B D n

section Sec52

variable {G : Type} [Group G]

@[expose] def oThreePrimeResidual (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ X ∧ ∃ k : ℕ, x ^ (3 ^ k) = 1}

@[expose] def IsBenderAny (X : Type) [Group X] : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ IsBenderCh5 k X

@[expose] def IsL2Choice (T H L₂ : Subgroup G) : Prop :=
  ∃ K₁ : Subgroup G, quasithinIsCComponent K₁ H ∧ oTwoUpper H = conjClosure K₁ T ∧
    ((IsBenderAny (O2Q K₁) ∧ L₂ = K₁) ∨
      (¬ IsBenderAny (O2Q K₁) ∧ K₁ = oTwoUpper H ∧
        ∃ P : Subgroup G, IsMaxParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P ∧
          quasithinIsCComponent L₂ P))

abbrev sec52S (M H : Subgroup G) : Subgroup G := pCoreOf 2 (M ⊓ H)

abbrev sec52G1 (M L H B L₂ : Subgroup G) : Subgroup G := L ⊔ sec52S M H ⊔ (B ⊓ L₂)

abbrev sec52G2 (M H D L₂ : Subgroup G) : Subgroup G := D ⊔ sec52S M H ⊔ L₂

noncomputable abbrev sec52Alpha (M L H B D L₂ : Subgroup G) : RankTwoAmalgam.{0} :=
  RankTwoAmalgam.ofSubgroups (sec52G1 M L H B L₂) (sec52G2 M H D L₂)

noncomputable abbrev sec52AlphaPrime (M L H B D : Subgroup G) : RankTwoAmalgam.{0} :=
  RankTwoAmalgam.ofSubgroups (L ⊔ (sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H))
    (D ⊔ (sec52S M H ⊓ L) ⊔ oTwoUpper H)

@[expose] def IsOmega4MinusBlock (L : Subgroup G) (m : ℕ) : Prop :=
  IsBlock2 L L ∧ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 (2 * m) ∧
    ∃ _ : IsMulCommutative ↥(blockU L), BinaryOrthogonalFour (V := ↥(blockU L))
      (autOn L (blockU L)) ⊤ ((blockZ L).subgroupOf (blockU L)) m

end Sec52

structure Hyp5_2_4 (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ) :
    Prop extends Hyp5_1_8 G T M L H n where
  notation59 : IsNotation5_1_9 T M L H B D
  ch5Module : IsCh5Module T L V
  notL34 : ¬ LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2
  D_le : D ≤ Subgroup.normalizer (oTwoUpper H : Set G)
  choice : IsL2Choice T H L₂

@[expose] def Cases5_2_6 {G : Type} [Group G] (α : RankTwoAmalgam.{0}) (L K : Subgroup G)
    (n : ℕ) : Prop :=
  (IsAmalgamOfGroup α (IsLieOverTwo .PSL 3 n) ∧ IsBlock2 L L ∧ IsLin2Type L n ∧
      IsBlock2 K K ∧ IsLin2Type K n) ∨
    (IsAmalgamOfGroup α (IsLieOverTwo .PSp 2 n) ∧ IsBlock2 L L ∧ IsLin2Type L n ∧
      IsBlock2 K K ∧ IsLin2Type K n) ∨
    (IsAmalgamOfGroup α (IsLieOverTwo .G2 0 n) ∧ IsL2Quot n (oTwoQuot ↥L) ∧
      IsL2Quot n (oTwoQuot ↥K) ∧ IsSpecialPow 2 (2 ^ n) 2 ↥(pCoreOf 2 K) ∧
      Nat.card (pCoreOf 2 L) = (2 ^ n) ^ 5) ∨
    (IsAmalgamOfGroup α (IsLieOverTwo .trialityD4 0 n) ∧ IsL2Quot n (oTwoQuot ↥L) ∧
      Nat.card (pCoreOf 2 L) = (2 ^ n) ^ 11 ∧ IsL2Quot (3 * n) (oTwoQuot ↥K) ∧
      IsSpecialPow 2 (2 ^ n) 4 ↥(pCoreOf 2 K)) ∨
    (IsAmalgamOfGroup α (IsLieOverTwo .twistedF4 0 n) ∧ IsL2Quot n (oTwoQuot ↥L) ∧
      Nat.card (pCoreOf 2 L) = (2 ^ n) ^ 11 ∧
      (∃ a : ℕ, n = 2 * a + 1 ∧ Nonempty (oTwoQuot ↥K ≃* Sz a)) ∧
      Nat.card (pCoreOf 2 K) = (2 ^ n) ^ 10) ∨
    (∃ m : ℕ, n = 2 * m ∧ 2 < n ∧
      (IsAmalgamOfGroup α (IsLieOverTwo .PSU 4 m) ∨ IsU4ExtTwo m α) ∧
      IsOmega4MinusBlock L m ∧ IsL2Quot m (oTwoQuot ↥K) ∧
      IsSpecialPow 2 (2 ^ m) 2 ↥(pCoreOf 2 K)) ∨
    (n = 4 ∧ IsAmalgamOfGroup α (IsLieOverTwo .PSU 5 2) ∧ IsL2Quot 4 (oTwoQuot ↥L) ∧
      Nat.card (pCoreOf 2 L) = 2 ^ 16 ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ^ 2 ∧
        Nonempty (oTwoQuot ↥K ≃* CFSG.Open.StatedSU 3 4 F)) ∧
      IsSpecialPow 2 4 3 ↥(pCoreOf 2 K))

@[expose] def Stmt5_2_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n →
      IsWeakBNPair (sec52G1 M L H B L₂) (sec52G2 M H D L₂) ∧
      L₂ = oTwoUpper H ∧ oTwoUpper H = perfectCore (sec52G2 M H D L₂) ∧
      pCoreOf 2 (sec52G1 M L H B L₂) = pCoreOf 2 L ∧
      pCoreOf 2 (sec52G2 M H D L₂) = pCoreOf 2 (oTwoUpper H) ∧
      Cases5_2_6 (sec52Alpha M L H B D L₂) L (oTwoUpper H) n ∧
      pCoreOf 2 (oTwoUpper H ⊔ T) = pCoreOf 2 (oTwoUpper H ⊔ sec52S M H) ∧
      ((sec52S M H ≤ L ∧ sec52S M H ≤ oTwoUpper H ∧
          pCoreOf 2 (L ⊔ sec52S M H) = pCoreOf 2 L ∧
          pCoreOf 2 (oTwoUpper H ⊔ sec52S M H) = pCoreOf 2 (oTwoUpper H)) ∨
        (∃ m : ℕ, n = 2 * m ∧ 2 < n ∧ IsU4ExtTwo m (sec52Alpha M L H B D L₂) ∧
          ∃ t : G, orderOf t = 2 ∧ t ∉ pCoreOf 2 (oTwoUpper H) ∧
            pCoreOf 2 (oTwoUpper H ⊔ sec52S M H) =
              pCoreOf 2 (oTwoUpper H) ⊔ Subgroup.zpowers t ∧
            ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
              ∃ P : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F),
                IsMaxParabolic2 ⊤ P ∧
                Nonempty (↥(oTwoUpper H ⊓ Subgroup.centralizer ({t} : Set G)) ≃*
                  ↥(perfectCore P))))

@[expose] def Stmt5_2_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n →
      ((IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo .PSL 3 n) ∨
          IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo .PSp 2 n) ∨
          IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo .G2 0 n) ∨
          IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo .trialityD4 0 n) ∨
          IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo .twistedF4 0 n)) ∨
        (∃ m : ℕ, n = 2 * m ∧ 2 < n ∧
          IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo .PSU 4 m)) ∨
        (n = 4 ∧ IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo .PSU 5 2))) ∧
      (L ⊔ (sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H) = L ⊔ B ⊔ D ∧
        D ⊔ (sec52S M H ⊓ L) ⊔ oTwoUpper H = oTwoUpper H ⊔ B ⊔ D ∧
        (L ⊔ B ⊔ D) ⊓ (oTwoUpper H ⊔ B ⊔ D) = (sec52S M H ⊓ L) ⊔ B ⊔ D ∧
        sec52S M H ⊓ L = T ⊓ L ∧ sec52S M H ⊓ L = T ⊓ oTwoUpper H ∧
        sec52S M H ⊓ L = pCoreOf 2 ((L ⊔ B ⊔ D) ⊓ (oTwoUpper H ⊔ B ⊔ D))) ∧
      (pCoreOf 2 L = pCoreOf 2 (L ⊔ B ⊔ D ⊔ T) ∧
        pCoreOf 2 (oTwoUpper H) = pCoreOf 2 (oTwoUpper H ⊔ B ⊔ D ⊔ T))

@[expose] def Stmt5_2_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n →
      quasithinIsMaximalLocal T (oTwoUpper H) ∨
      (IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo .PSL 3 2) ∧
        ∃ K' : Subgroup G, oTwoUpper H < K' ∧ quasithinIsMaximalLocal T K' ∧
          CFSG.Quasithin.IsExcA7Block K')

section Types

variable {G : Type} [Group G]

@[expose] def IsOfLieType52 (M L H B D T : Subgroup G)
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ) : Prop :=
  IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo t m f) ∧
    quasithinIsMaximalLocal T (oTwoUpper H)

@[expose] def IsOfTypeM23 (M L H B D T : Subgroup G) : Prop :=
  IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo .PSL 3 2) ∧
    ¬ quasithinIsMaximalLocal T (oTwoUpper H)

end Types

@[expose] def Stmt5_2_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n →
      (∃ f : ℕ, 2 ≤ f ∧
        (IsOfLieType52 M L H B D T .PSL 3 f ∨ IsOfLieType52 M L H B D T .PSp 2 f ∨
          IsOfLieType52 M L H B D T .G2 0 f ∨ IsOfLieType52 M L H B D T .trialityD4 0 f ∨
          IsOfLieType52 M L H B D T .twistedF4 0 f)) ∨
      (∃ m : ℕ, n = 2 * m ∧ 2 < n ∧ IsOfLieType52 M L H B D T .PSU 4 m) ∨
      IsOfLieType52 M L H B D T .PSU 5 2 ∨
      IsOfTypeM23 M L H B D T

end CFSG.Quasithin.H13
