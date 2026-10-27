module

public import CFSG.LocalAnalysis.RankFourTheoremC.FullCoreRank4
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointProp31
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.ExcLines

public section

namespace CFSG.Yardstones.Md8ed6d263d89

open scoped MatrixGroups

@[expose] def YSFischerRankFourPending : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.LocalAnalysis.RankFourTheoremC.FischerRankFourPending G

@[expose] def TheoremCAt (G : Type) [Group G] [Finite G] (q : ℕ) (N : Subgroup G) : Prop :=
  CFSG.Open.GLBAlmostStrong N q ∧
    ∀ H : Subgroup G, CFSG.Open.IsTwoLocal H → 2 ≤ CFSG.Open.pRank q (H ⊓ N) → H ≤ N

@[expose] def sixPlane {G : Type} [Group G] (p : ℕ) (P : Subgroup G) (x : G) : Subgroup G :=
  Subgroup.zpowers x ⊔ CFSG.LocalAnalysis.RankFourTheoremC.PPointP.omegaCenter p P

@[expose] def IsLinTwoType (p : ℕ) (i : TauCeti.CFSGIndex) : Prop :=
  ∃ (d : TauCeti.ValidLieTypeIndex) (n : ℕ), 2 ≤ n ∧ i = TauCeti.CFSGIndex.lie d ∧
    CFSG.AGLEmbedding.IsLinTwoIndex p n d

@[expose] def IsUnitaryThreeType (p : ℕ) (i : TauCeti.CFSGIndex) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, i = TauCeti.CFSGIndex.lie d ∧
    CFSG.AGLEmbedding.IsUnitaryIndex p d ∧ d.1.fieldExponent = 1

@[expose] def PPointData {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G)
    (x : G) (R : Sylow p (CFSG.LocalAnalysis.RankFourTheoremC.RedCent p x))
    (K : Subgroup (CFSG.LocalAnalysis.RankFourTheoremC.RedCent p x)) (i : TauCeti.CFSGIndex) :
    Prop :=
  CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x ∧
    CFSG.LocalAnalysis.RankFourTheoremC.PPointFacts p M x R K i ∧
    (R : Subgroup (CFSG.LocalAnalysis.RankFourTheoremC.RedCent p x)) =
      (((P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
          (Subgroup.centralizer ({x} : Set G))).map
        (QuotientGroup.mk' (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
          (G := Subgroup.centralizer ({x} : Set G)) p))

@[expose] def YSPPointTypeLinTwoOrUnitary : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G → 4 ≤ CFSG.Open.evenRank G →
    CFSG.Open.GLBPreuniqueness G →
    CFSG.AGLEmbeddingD2.D1For G → CFSG.LocalAnalysis.RankFourTheoremC.FullCoreLocality G →
    ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x : G)
      (R : Sylow p (CFSG.LocalAnalysis.RankFourTheoremC.RedCent p x))
      (K : Subgroup (CFSG.LocalAnalysis.RankFourTheoremC.RedCent p x)) (i : TauCeti.CFSGIndex),
      5 ≤ p → CFSG.AGLEmbedding.D1Local p P M → PPointData p P M x R K i →
        IsLinTwoType p i ∨ IsUnitaryThreeType p i

@[expose] def YSPNonemptyConfinement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G → 4 ≤ CFSG.Open.evenRank G →
    CFSG.Open.GLBPreuniqueness G →
    CFSG.AGLEmbeddingD2.D1For G → CFSG.LocalAnalysis.RankFourTheoremC.D2For G →
    CFSG.LocalAnalysis.RankFourTheoremC.FullCoreLocality G →
    ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), 5 ≤ p → CFSG.AGLEmbedding.D1Local p P M →
      (∃ x : G, CFSG.LocalAnalysis.RankFourTheoremC.IsPElement p M x) →
      (∀ (x : G) (R : Sylow p (CFSG.LocalAnalysis.RankFourTheoremC.RedCent p x))
        (K : Subgroup (CFSG.LocalAnalysis.RankFourTheoremC.RedCent p x)) (i : TauCeti.CFSGIndex),
        PPointData p P M x R K i → IsLinTwoType p i ∨ IsUnitaryThreeType p i) →
      (∀ H : Subgroup G, CFSG.Open.IsTwoLocal H → 2 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M) ∧
        ∀ (x : G) (R : Sylow p (CFSG.LocalAnalysis.RankFourTheoremC.RedCent p x))
          (K : Subgroup (CFSG.LocalAnalysis.RankFourTheoremC.RedCent p x))
          (i : TauCeti.CFSGIndex), PPointData p P M x R K i → IsLinTwoType p i

@[expose] def YSPPointCentralizers : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G → 4 ≤ CFSG.Open.evenRank G →
    CFSG.Open.GLBPreuniqueness G →
    CFSG.AGLEmbeddingD2.D1For G → CFSG.LocalAnalysis.RankFourTheoremC.FullCoreLocality G →
    ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x : G), 5 ≤ p →
      CFSG.AGLEmbedding.D1Local p P M → CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x →
      (∀ H : Subgroup G, CFSG.Open.IsTwoLocal H → 2 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M) →
      IsMulCommutative (P : Subgroup G) →
      (∀ g : G, CFSG.Open.GLBConj g (Subgroup.zpowers x) ≤ (P : Subgroup G) →
        CFSG.Open.GLBConj g (Subgroup.zpowers x) = Subgroup.zpowers x) →
      ((∃ (_ : Fact p.Prime) (n : ℕ), 2 ≤ n ∧
          Nonempty (CFSG.Open.GLBLayer
              (Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) ≃*
            PSL(2, GaloisField p n))) ∧
        ¬ CFSG.Open.GLBLayer
            (Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) ≤ M ∧
        ∀ S : Subgroup G,
          S ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) ⊓
            Subgroup.centralizer (CFSG.Open.GLBLayer
              (Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) : Set G) →
          IsPGroup p S → IsCyclic S) ∧
      ∀ P₁ : Subgroup G, P₁ ≤ (P : Subgroup G) → Nat.card P₁ = p →
        P₁ ≠ Subgroup.zpowers x → Subgroup.normalizer (P₁ : Set G) ≤ M

@[expose] def YSPPointFrobenius : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G → 4 ≤ CFSG.Open.evenRank G →
    CFSG.Open.GLBPreuniqueness G →
    CFSG.AGLEmbeddingD2.D1For G → CFSG.LocalAnalysis.RankFourTheoremC.FullCoreLocality G →
    ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x : G), 5 ≤ p →
      CFSG.AGLEmbedding.D1Local p P M → CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x →
      (∀ H : Subgroup G, CFSG.Open.IsTwoLocal H → 2 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M) →
      IsMulCommutative (P : Subgroup G) →
      (∀ g : G, CFSG.Open.GLBConj g (Subgroup.zpowers x) ≤ (P : Subgroup G) →
        CFSG.Open.GLBConj g (Subgroup.zpowers x) = Subgroup.zpowers x) →
      (∀ P₁ : Subgroup G, P₁ ≤ (P : Subgroup G) → Nat.card P₁ = p →
        P₁ ≠ Subgroup.zpowers x → Subgroup.normalizer (P₁ : Set G) ≤ M) →
      (∃ (_ : Fact p.Prime) (n : ℕ), 2 ≤ n ∧
        Nonempty (CFSG.Open.GLBLayer
            (Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) ≃*
          PSL(2, GaloisField p n))) →
      ¬ CFSG.Open.GLBLayer (Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) ≤
        M →
      (∀ S : Subgroup G,
        S ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) ⊓
          Subgroup.centralizer (CFSG.Open.GLBLayer
            (Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) : Set G) →
        IsPGroup p S → IsCyclic S) →
      Group.IsSolvable M ∧
        CFSG.Open.GLBIsFrobenius (CFSG.Open.GLBPrimeCore p M ⊔ Subgroup.zpowers x)
          (CFSG.Open.pCoreOf 2 M)
          (CFSG.Open.GLBPrimeCore p
              (Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) ⊔
            Subgroup.zpowers x)

@[expose] def YSPEmptyPlaneLocals : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G → 4 ≤ CFSG.Open.evenRank G →
    CFSG.Open.GLBPreuniqueness G →
    CFSG.AGLEmbeddingD2.D1For G → CFSG.LocalAnalysis.RankFourTheoremC.D2For G →
    CFSG.LocalAnalysis.RankFourTheoremC.FullCoreLocality G →
    (∀ (f : ℕ) (F : Sylow f G) (N : Subgroup G), CFSG.AGLEmbedding.D1Local f F N →
      (∃ y : G, CFSG.LocalAnalysis.RankFourTheoremC.IsPElement f N y) → TheoremCAt G f N) →
    ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), 5 ≤ p →
      (∀ (q : ℕ) (Q : Sylow q G) (N : Subgroup G), p < q → CFSG.AGLEmbedding.D1Local q Q N →
        TheoremCAt G q N) →
      CFSG.AGLEmbedding.D1Local p P M →
      (¬ ∃ x : G, CFSG.LocalAnalysis.RankFourTheoremC.IsPElement p M x) →
      ∀ x : G, x ∈ (P : Subgroup G) → orderOf x = p →
        ¬ Subgroup.centralizer ({x} : Set G) ≤ M →
        CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G))
          (Subgroup.centralizer ({x} : Set G)) →
        ∀ H : Subgroup G, CFSG.Open.IsTwoLocal H → sixPlane p (P : Subgroup G) x ≤ H →
          (∃ S : Subgroup G, S ≤ H ⊓ M ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
            sixPlane p (P : Subgroup G) x ≤ Subgroup.normalizer (S : Set G)) →
          H ≤ M

@[expose] def YSPEmptyStrongOfPlaneLocals : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G → 4 ≤ CFSG.Open.evenRank G →
    CFSG.Open.GLBPreuniqueness G →
    CFSG.AGLEmbeddingD2.D1For G → CFSG.LocalAnalysis.RankFourTheoremC.D2For G →
    CFSG.LocalAnalysis.RankFourTheoremC.FullCoreLocality G →
    (∀ (f : ℕ) (F : Sylow f G) (N : Subgroup G), CFSG.AGLEmbedding.D1Local f F N →
      (∃ y : G, CFSG.LocalAnalysis.RankFourTheoremC.IsPElement f N y) → TheoremCAt G f N) →
    ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), 5 ≤ p →
      (∀ (q : ℕ) (Q : Sylow q G) (N : Subgroup G), p < q → CFSG.AGLEmbedding.D1Local q Q N →
        TheoremCAt G q N) →
      CFSG.AGLEmbedding.D1Local p P M →
      (¬ ∃ x : G, CFSG.LocalAnalysis.RankFourTheoremC.IsPElement p M x) →
      (∀ x : G, x ∈ (P : Subgroup G) → orderOf x = p →
        ¬ Subgroup.centralizer ({x} : Set G) ≤ M →
        CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G))
          (Subgroup.centralizer ({x} : Set G)) →
        ∀ H : Subgroup G, CFSG.Open.IsTwoLocal H → sixPlane p (P : Subgroup G) x ≤ H →
          (∃ S : Subgroup G, S ≤ H ⊓ M ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
            sixPlane p (P : Subgroup G) x ≤ Subgroup.normalizer (S : Set G)) →
          H ≤ M) →
      CFSG.Open.GLBStronglyEmbedded p M

end CFSG.Yardstones.Md8ed6d263d89
