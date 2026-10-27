module

public import CFSG.Quasithin.Vol2.Ch5Statements
public import CFSG.Quasithin.Background.A3Structure314Defs
public import CFSG.Quasithin.H13.StatementsVocab
public import CFSG.Quasithin.Background.G2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative Pointwise

section Vocabulary

variable {G : Type} [Group G]

@[expose] def o2Img (X Y : Subgroup G) : Subgroup (O2Q X) :=
  (Y.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))

@[expose] def IsLieTypeChar2 (X : Type) [Group X] : Prop :=
  EvenLieType (X ⧸ Subgroup.center X)

@[expose] def IsHatComp (X K₁ Kh₁ : Subgroup G) : Prop :=
  quasithinIsCComponent Kh₁ X ∧ K₁ ≤ Kh₁ ∧
    ∀ Y : Subgroup G, quasithinIsCComponent Y X → K₁ ≤ Y → Y = Kh₁

end Vocabulary

@[expose] def Stmt5_1_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L H B D K₁ : Subgroup G) (n k : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsFieldParam510 T H k →
    quasithinIsCComponent K₁ H → oTwoUpper H = conjClosure K₁ T →
    ∀ X : Subgroup G, InH H X →
      ∃ Kh₁ : Subgroup G, IsHatComp X K₁ Kh₁ ∧ oTwoUpper H ≤ conjClosure Kh₁ T ∧
        (oTwoUpper H = conjClosure Kh₁ T ∨
          (K₁ < oTwoUpper H ∧ LieModel (O2Q K₁) .PSL 2 2 2 ∧
            (IsSporadic .J1 (O2Q Kh₁) ∨
              ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
                IsPSL 2 p 1 (O2Q Kh₁))) ∨
          (SuzukiModel (O2Q (oTwoUpper H)) 2 k ∧ Is2F4 k (O2Q (conjClosure Kh₁ T))) ∨
          (LieModel (O2Q (oTwoUpper H)) .PSL 2 2 k ∧
            IsRank2LieChar2 (O2Q (conjClosure Kh₁ T))) ∨
          (LieModel (O2Q (oTwoUpper H)) .PSL 2 2 2 ∧ oTwoUpper H < conjClosure Kh₁ T ∧
            ¬ IsLieTypeChar2 (O2Q (conjClosure Kh₁ T)) ∧
            A314Statement (o2Img X T) (o2Img X (oTwoUpper H)) (o2Img X (conjClosure Kh₁ T))))

@[expose] def Stmt5_1_14_first : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 →
      (quasithinIsMaximalLocal T (oTwoUpper H) ∧
          IsUniqueM H (Subgroup.normalizer (oTwoUpper H : Set G)) ∧
          ¬ quasithinIsFaithfulLocal T (oTwoUpper H)) ∧
        (⁅quasithinOmegaOneCenter T, H⁆ = ⊥ ∧
          ∀ z ∈ quasithinOmegaOneCenter T, z ≠ 1 →
            Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (oTwoUpper H : Set G)) ∧
        quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥

@[expose] def Stmt5_1_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 →
      D ≤ Subgroup.normalizer (oTwoUpper H : Set G) ∨
      (n = 2 ∧ IsSumOfTwo L V (fun W => IsNatModCh5 L W n)) ∨
      ((n = 2 ∨ n = 4) ∧ IsNatModCh5 L ⁅V, L⁆ n) ∨
      ((n = 4 ∨ n = 8) ∧ IsOrthCh5 L V n ∧
        ∀ Dm : Subgroup G, Dm ≤ D → Nat.card Dm = 2 ^ (n / 2) + 1 →
          Dm ≤ Subgroup.normalizer (oTwoUpper H : Set G))

@[expose] def Stmt5_1_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 →
      ¬ 3 ∣ Nat.card ↥(centralizerModO2 (oTwoUpper H)) ∧
      (¬ Group.IsSolvable ↥(centralizerModO2 (oTwoUpper H)) →
        (∃ k : ℕ, SuzukiModel (O2Q (perfectCore (centralizerModO2 (oTwoUpper H)))) 2 k) ∧
        ¬ perfectCore (centralizerModO2 (oTwoUpper H)) ≤ M ∧
        ¬ D ≤ Subgroup.normalizer (oTwoUpper H : Set G))

@[expose] def Stmt5_1_17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → Even n

@[expose] def Stmt5_1_18 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 →
      ∀ D₃ : Subgroup G, D₃ ≤ D → Nat.card D₃ = 3 →
        D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G) →
          D₃ = B ∧ ⁅quasithinOmegaOneCenter T, D₃⁆ = ⊥

@[expose] def Concl5_1_14_four {G : Type} [Group G] (T L V B D : Subgroup G) (n : ℕ) : Prop :=
  n = 2 ∧
    ((IsBarS5 L T V ∧ (IsS5ModCh5 L T V ∨ IsSumOfTwo (L ⊔ T) V (IsS5ModCh5 L T))) ∨
      IsOrthCh5 L V 2) ∧
    D = B

@[expose] def Stmt5_1_19 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ Concl5_1_14_four T L V B D n →
      ∀ D₃ : Subgroup G, D₃ ≤ D → Nat.card D₃ = 3 →
        (¬ D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G) ∧
            ((n = 2 ∧ IsSumOfTwo L V (fun W => IsNatModCh5 L W n)) ∨
              ((n = 2 ∨ n = 4) ∧ IsNatModCh5 L ⁅V, L⁆ n))) ∨
          ((n = 4 ∨ n = 8) ∧ IsOrthCh5 L V n ∧
            ¬ D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G)) ∨
          (n % 4 = 2 ∧ 2 < n ∧ ¬ 3 ∣ n ∧ D₃ = B ∧
            D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G) ∧ IsOrthCh5 L V n)

@[expose] def Stmt5_1_20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ Concl5_1_14_four T L V B D n →
      ∀ D₃ : Subgroup G, D₃ ≤ D → Nat.card D₃ = 3 →
        ¬ D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G) ∧ pCoreOf 2 (H ⊔ D₃) = ⊥

section Z1

variable {G : Type} [Group G]

@[expose] def IsZ1Choice (T L Z₁ : Subgroup G) : Prop :=
  Z₁ ≤ quasithinOmegaOneCenter T ∧ Nat.card Z₁ = 2 ∧
    (Z₁ = quasithinOmegaOneCenter T ∨
      (IsSumOfTwo L (conjClosure (quasithinOmegaOneCenter T) L) (fun W => IsNatModCh5 L W 2) ∧
        ∃ V₁ : Subgroup G, IsIrrPlusBase L (conjClosure (quasithinOmegaOneCenter T) L) V₁ ∧
          Z₁ = quasithinOmegaOneCenter T ⊓ V₁))

end Z1

@[expose] def Stmt5_1_21 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D D₃ Z₁ H₁ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ Concl5_1_14_four T L V B D n →
    D₃ ≤ D → Nat.card D₃ = 3 → IsZ1Choice T L Z₁ →
    H ≤ H₁ → H₁ ≤ Subgroup.centralizer (Z₁ : Set G) →
      ⁅conjClosure (conjClosure Z₁ D₃) H₁, pCoreOf 2 H₁⁆ ≤ Z₁ ∧
        frattiniOf (conjClosure (conjClosure Z₁ D₃) H₁) ≤ Z₁

@[expose] def Stmt5_1_22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D D₃ Z₁ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ Concl5_1_14_four T L V B D n →
    D₃ ≤ D → Nat.card D₃ = 3 → IsZ1Choice T L Z₁ →
      (Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) =
          (T ⊓ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G)) ⊔ B ∧
        Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) ≤ M) ∧
      ((n = 2 ∨ n = 4) ∧
        (IsNatModCh5 L ⁅V, L⁆ n ∨ IsSumOfTwo L ⁅V, L⁆ (fun W => IsNatModCh5 L W n))) ∧
      (⁅conjClosure Z₁ D₃, pCoreOf 2 (oTwoUpper H)⁆ = Z₁ ∧
        Subgroup.normalizer (conjClosure Z₁ D₃ : Set G) ≤ Subgroup.normalizer
          ((D₃ ⊔ pCoreOf 2 (Subgroup.centralizer (conjClosure Z₁ D₃ : Set G)) : Subgroup G) :
            Set G))

@[expose] def Stmt5_1_23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D D₃ Z₁ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ Concl5_1_14_four T L V B D n →
    D₃ ≤ D → Nat.card D₃ = 3 → IsZ1Choice T L Z₁ →
      IsMulCommutative ↥(conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))

@[expose] def Stmt5_2_L2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsL2Choice T H L₂ →
      IsSylowTwoOf (T ⊓ L₂) L₂ ∧ oTwoUpper H = conjClosure L₂ T

@[expose] def Stmt5_2_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsL2Choice T H L₂ →
    ¬ LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 →
      sec52S M H ≤ Subgroup.normalizer (L₂ : Set G)

@[expose] def Stmt5_2_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n →
      D ≤ Subgroup.normalizer (oTwoUpper H : Set G) ∧
      (D ≤ Subgroup.normalizer (B : Set G) ∧ B ≤ Subgroup.normalizer (D : Set G)) ∧
      (B ≤ Subgroup.normalizer (sec52S M H : Set G) ∧
        D ≤ Subgroup.normalizer ((sec52S M H ⊓ L₂ : Subgroup G) : Set G) ∧
        (D : Set G) * (sec52S M H : Set G) = (sec52S M H : Set G) * (D : Set G)) ∧
      D ⊔ sec52S M H ⊔ B ≤ Subgroup.normalizer (L₂ : Set G)

@[expose] def StmtF11_5_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → Hyp111 L L₂ (sec52S M H)

end CFSG.Quasithin.H13
