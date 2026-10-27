module

public import CFSG.LocalAnalysis.RankThreeUC.Asc1930

public section

namespace CFSG.Yardstones.Mf4cdcdf2e013

open Subgroup
open scoped MatrixGroups
open CFSG.LocalAnalysis.RankThreeUC (hSet uCore Asc1930)

structure Standing4 (G : Type) [Group G] [Finite G] : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : CFSG.Open.IsKProper G
  charTwo : CFSG.Open.IsCharTwoType G
  rank : 4 ≤ CFSG.Open.evenRank G

variable {G : Type} [Group G] [Finite G]

@[expose] def UniqueFourClauseTwoAt (M : Subgroup G) (p : ℕ) : Prop :=
  ∃ P : Sylow p G, (P : Subgroup G) ≤ M ∧ CFSG.Open.uniqueFourGamma p P ≤ M ∧ 5 ≤ p ∧
    Group.IsSolvable M ∧ IsMulCommutative (P : Subgroup G) ∧
      ∃ P₀ : Subgroup G, CFSG.Open.uniqueFourClauseTwo M P P₀ p

@[expose] def SigmaTwo4 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p ∈ CFSG.Open.uniqueFourBeta G ∧ ∃ M : Subgroup G, CFSG.Open.uniqueFourIsMaxTwoLocal M ∧
    p ∈ CFSG.Open.uniqueFourSigma M ∧ UniqueFourClauseTwoAt M p

@[expose] def SigmaChoice4 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  (3 ∈ CFSG.Open.uniqueFourBeta G → p = 3) ∧
    (3 ∉ CFSG.Open.uniqueFourBeta G → (∃ q, SigmaTwo4 G q) → SigmaTwo4 G p)

@[expose] def SigmaOne4 (G : Type) [Group G] [Finite G] : Set ℕ :=
  {p | p ∈ CFSG.Open.uniqueFourBeta G ∧ ∃ N : Subgroup G, CFSG.Open.uniqueFourIsMaxTwoLocal N ∧
    p ∈ CFSG.Open.uniqueFourSigma N ∧ CFSG.RankThree.PartOne.IsStronglyPEmbedded p N}

structure Setup4 (G : Type) [Group G] [Finite G] where
  p : ℕ
  M : Subgroup G
  maxLocal : CFSG.Open.uniqueFourIsMaxTwoLocal M
  hp : p ∈ CFSG.Open.uniqueFourSigma M
  T : Subgroup G
  sylowM : CFSG.ABGLocalTools.IsSylowOf 2 T M
  sylowG : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤
  normalizer_le : normalizer (T : Set G) ≤ M
  notCatalog : ¬ CFSG.Blueprint.Catalog G
  hSet_nonempty : (hSet T M).Nonempty
  V : Subgroup G
  le : V ≤ M
  le_normalizer : M ≤ normalizer (V : Set G)
  elemAbelian : CFSG.Open.IsElemAbelian 2 V
  not_isTI : ¬ CFSG.CGT.Timmesfeld75.IsTI V

@[expose] def Setup4.InMSigma (S : Setup4 G) : Prop :=
  SigmaChoice4 G S.p

@[expose] def TheoremCAt (M : Subgroup G) : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ Q : Subgroup G, Q ≤ M → IsPGroup q Q → 2 ≤ CFSG.Open.pRank q Q →
    CFSG.Open.rankThreeGamma 1 q Q ≤ M → ∀ H : Subgroup G, CFSG.Open.IsTwoLocal H → Q ≤ H → H ≤ M

@[expose] def Theorem614At (M : Subgroup G) : Prop :=
  CFSG.Open.uniqueFourSigma M ⊆ SigmaOne4 G →
    ∀ r : ℕ, r.Prime → r ≠ 2 → r ∉ CFSG.Open.uniqueFourSigma M →
      ∀ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf r R M →
        ∀ E : Subgroup G, E ≤ R ⊓ centralizer (R : Set G) → CFSG.Open.IsElemAbelian r E →
          Nat.card E = r ^ 2 → CFSG.Open.rankThreeGamma 1 r E ≤ M →
            CFSG.RankThree.PartOne.IsStronglyPEmbedded r M

@[expose] def QuasisimpleModOTwo (L : Subgroup G) : Prop :=
  ∃ h : (CFSG.Open.pCore 2 ↥L).Normal,
    @CFSG.Open.IsQuasisimple (↥L ⧸ CFSG.Open.pCore 2 ↥L)
      (@QuotientGroup.Quotient.group ↥L _ (CFSG.Open.pCore 2 ↥L) h)

@[expose] def Asc83CComponent (M L : Subgroup G) : Prop :=
  L ≤ M ∧ CFSG.Open.IsSubnormal L M ∧ ⁅L, L⁆ = L ∧ QuasisimpleModOTwo L

@[expose] def Hyp81 (M L : Subgroup G) : Prop :=
  L ≤ M ∧ CFSG.Open.IsSubnormal L M ∧ ⁅L, L⁆ = L ∧ 3 ≤ CFSG.Open.pRank 3 L ∧
    (QuasisimpleModOTwo L ∨
      ∃ L₁ L₂ L₃ : Subgroup G, L = L₁ ⊔ L₂ ⊔ L₃ ∧
        L₁ ≤ L ∧ L₂ ≤ L ∧ L₃ ≤ L ∧
          Asc83CComponent M L₁ ∧ CFSG.Open.pRank 3 L₁ = 1 ∧
            Asc83CComponent M L₂ ∧ CFSG.Open.pRank 3 L₂ = 1 ∧
              Asc83CComponent M L₃ ∧ CFSG.Open.pRank 3 L₃ = 1 ∧
                ∀ element : G, element ∈ L →
                  ∃ firstElement ∈ L₁, ∃ secondElement ∈ L₂, ∃ thirdElement ∈ L₃,
                    element = firstElement * secondElement * thirdElement)

@[expose] def Theorem82At (M : Subgroup G) : Prop :=
  ∀ L : Subgroup G, Hyp81 M L → CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 M

@[expose] def PartIAt (M : Subgroup G) : Prop :=
  TheoremCAt M ∧ Theorem614At M ∧ Theorem82At M

@[expose] def InCalV (M V : Subgroup G) : Prop :=
  V ≠ ⊥ ∧ CFSG.Open.IsElemAbelian 2 V ∧ V ≤ M ∧ M ≤ normalizer (V : Set G)

@[expose] def OTwoQuotTrivial (M K : Subgroup G) : Prop :=
  ∀ N : Subgroup G, K ≤ N → N ≤ M → M ≤ normalizer (N : Set G) →
    (∀ x ∈ N, ∃ k : ℕ, x ^ (2 ^ k) ∈ K) → N = K

@[expose] def InCalV1 (M T V : Subgroup G) : Prop :=
  InCalV M V ∧ ∀ N : Subgroup G, CFSG.Open.uniqueFourIsMaxTwoLocal N →
    M ⊓ normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) : Set G) ≤ N → N = M

@[expose] def InCalW (M T V : Subgroup G) : Prop :=
  InCalV1 M T V ∧ 8 ≤ Nat.card V ∧ OTwoQuotTrivial M (M ⊓ centralizer (V : Set G))

@[expose] def InCalWStar (M T V : Subgroup G) : Prop :=
  InCalW M T V ∧ ∀ U : Subgroup G, InCalW M T U → U ≤ V → U = V

@[expose] def InCalV0 (M V₀ V : Subgroup G) : Prop :=
  InCalV M V₀ ∧ InCalV M V ∧ V₀ ≤ V ∧ CFSG.CGT.Timmesfeld75.IsTI V₀ ∧
    ¬ CFSG.CGT.Timmesfeld75.IsTI V ∧
    (∀ v ∈ V, v ∉ V₀ → (⨆ m : M, (zpowers v).map (MulAut.conj (m : G)).toMonoidHom) = V) ∧
    ¬ OTwoQuotTrivial M (M ⊓ centralizer (V : Set G))

@[expose] def Hyp122 (M T V₀ V : Subgroup G) : Prop :=
  InCalV0 M V₀ V ∧
    (∀ z ∈ T, (∀ y ∈ T, z * y = y * z) → z ≠ 1 →
      centralizer ({z} : Set G) ≤ M ∧
        ∀ g : G, g ∉ M → ¬ centralizer ({z} : Set G) ≤ CFSG.Open.uniqueFourConj g M) ∧
    ∀ U : Subgroup G, ¬ InCalW M T U

@[expose] def Hyp123 (M T V₀ V : Subgroup G) : Prop :=
  (InCalWStar M T V ∧ V₀ = ⊥) ∨ Hyp122 M T V₀ V

@[expose] def CentralizesQuot (V₀ V : Subgroup G) (t : G) : Prop :=
  ∀ v ∈ V, v⁻¹ * (t * v * t⁻¹) ∈ V₀

@[expose] def MinCodimGt (M V₀ V : Subgroup G) (n : ℕ) : Prop :=
  (∀ t ∈ M, ¬ CentralizesQuot V₀ V t → CentralizesQuot V₀ V (t * t) →
      2 ^ (n + 1) * Nat.card {v : G // v ∈ V ∧ v⁻¹ * (t * v * t⁻¹) ∈ V₀} ≤ Nat.card V) ∧
    ((∀ t ∈ M, CentralizesQuot V₀ V (t * t) → CentralizesQuot V₀ V t) →
      2 ^ (n + 1) * Nat.card V₀ ≤ Nat.card V)

@[expose] def Theorem1669At (M T : Subgroup G) : Prop :=
  ∀ V₀ V H₀ : Subgroup G, Hyp123 M T V₀ V → H₀ ∈ hSet T M →
    CFSG.LocalAnalysis.RankThreeUC.Hyp124 M H₀ → Nat.card V₀ ≤ 4 → MinCodimGt M V₀ V 3

@[expose] def AGL81TheoremDFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing4 G → CFSG.Open.uniqueFourUnique G →
    ∀ (p : ℕ) (M : Subgroup G), CFSG.Open.uniqueFourIsMaxTwoLocal M →
      p ∈ CFSG.Open.uniqueFourSigma M → ∀ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 T M →
        normalizer (T : Set G) ≤ M

@[expose] def AGL81TheoremCFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing4 G → CFSG.Open.uniqueFourUnique G →
    ∀ (p : ℕ) (M : Subgroup G), CFSG.Open.uniqueFourIsMaxTwoLocal M →
      p ∈ CFSG.Open.uniqueFourSigma M → TheoremCAt M

@[expose] def CatalogNoUniqueFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing4 G → CFSG.Blueprint.Catalog G →
    ¬ CFSG.Open.uniqueFourUnique G

@[expose] def Theorem614Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing4 G → CFSG.Open.uniqueFourUnique G →
    ∀ S : Setup4 G, S.InMSigma → TheoremCAt S.M → Theorem614At S.M

@[expose] def Theorem82Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing4 G → CFSG.Open.uniqueFourUnique G →
    ∀ S : Setup4 G, S.InMSigma → TheoremCAt S.M → Theorem614At S.M → Theorem82At S.M

@[expose] def Theorem1669Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing4 G → CFSG.Open.uniqueFourUnique G →
    ∀ S : Setup4 G, S.InMSigma → PartIAt S.M → Theorem1669At S.M S.T

@[expose] def Theorem1930Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing4 G → CFSG.Open.uniqueFourUnique G →
    ∀ S : Setup4 G, S.InMSigma → PartIAt S.M → Theorem1669At S.M S.T →
      ∀ H ∈ hSet S.T S.M, Asc1930 S.M H

@[expose] def Theorem2219Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing4 G → CFSG.Open.uniqueFourUnique G →
    ∀ S : Setup4 G, S.InMSigma → PartIAt S.M → (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) →
      CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T)

@[expose] def Section23Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing4 G → CFSG.Open.uniqueFourUnique G →
    ∀ S : Setup4 G, S.InMSigma → PartIAt S.M → (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) →
      CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T) → False

end CFSG.Yardstones.Mf4cdcdf2e013
