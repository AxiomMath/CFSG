module

public import CFSG.Quasithin.Vol2.Ch6Inputs
public import CFSG.Quasithin.Background.F7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.Vol2.Ch6Defs
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def Stmt6_1_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp611 G T M L V n →
    (IsSumOfTwo L V (fun W => IsNatModCh5 L W n) ∨ IsNatQuotCh5 L ⁅V, L⁆ n ∨
      (2 < n ∧ IsOrthCh5 L V n)) ∧
    (IsNatQuotCh5 L ⁅V, L⁆ n ∨
      (thompsonJ T ≤ ch6Q T V ∧ ch6Q T V = pCoreOf 2 (L ⊔ T) ∧
        L ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G) ∧
        IsUniqueM (Subgroup.normalizer (thompsonJ T : Set G)) M))

@[expose] def Stmt6_1_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp611 G T M L V n →
    IsNatQuotCh5 L ⁅V, L⁆ n

@[expose] def Stmt6_1_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp611 G T M L V n →
    ∀ H : Subgroup G, IsHStar T M H →
      H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)

@[expose] def Stmt6_1_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp611 G T M L V n →
    (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
      T ⊓ Subgroup.centralizer (L : Set G) = ⊥) ∧
    (IsNatModCh5 L ⁅V, L⁆ n ∧ (⁅L, thompsonJ T⁆ = L → V = ⁅V, L⁆)) ∧
    ⁅V, L⁆ = ⁅reducedAggregate (L ⊔ T), L⁆

structure Hyp611Nat (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ) : Prop
    extends Hyp611 G T M L V n where
  comm_eq : ⁅V, L⁆ = V
  natural : IsNatModCh5 L V n

@[expose] def Stmt6_1_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp611Nat G T M L V n →
    (n : ℕ∞) ≤ rParam V ∧
    (∀ hV : IsElemAbelian 2 V, sParam hV = n ∧ mParam (autI hV M) = n) ∧
    ∀ g : G, conjSubgroup V g ≤ Subgroup.normalizer (V : Set G) →
      ¬ conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) →
      mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.centralizer (V : Set G)) = n

@[expose] def Stmt6_1_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp611Nat G T M L V n →
    ∀ g : G, conjSubgroup V g ≤ T → ⁅V, conjSubgroup V g⁆ ≠ ⊥ →
      ⁅V, conjSubgroup V g⁆ ≤ V ⊓ conjSubgroup V g →
      ch6ZS T L V = ⁅V, conjSubgroup V g⁆ ∧ ch6ZS T L V = V ⊓ conjSubgroup V g ∧
      ∃ c ∈ Subgroup.centralizer (ch6ZS T L V : Set G), conjSubgroup V g = conjSubgroup V c

@[expose] def Stmt6_1_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp611Nat G T M L V n →
    (¬ Subgroup.normalizer (wClos V 0 T : Set G) ≤ M ∨
      ¬ Subgroup.centralizer (cClos V 1 T : Set G) ≤ M) ∧
    (2 < n → ch6ZS T L V ≤ cClos V 1 T) ∧
    wClos V 0 T ≤ ch6S T L V

@[expose] def Stmt6_1_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp611Nat G T M L V n →
    ∀ U : Subgroup G, U ≤ V → mQuot V U = n →
      Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) ∨
      (∃ l ∈ L, U = conjSubgroup (ch6ZS T L V) l) ∨
      (Even n ∧ ∃ t ∈ M, IsInvolutoryFieldAut L t ∧ U = V ⊓ Subgroup.centralizer ({t} : Set G))

@[expose] def Stmt6_1_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp611Nat G T M L V n →
    Even n → ∀ t ∈ T, IsInvolutoryFieldAut L t →
    ∀ U : Subgroup G, U = V ⊓ Subgroup.centralizer ({t} : Set G) →
    IsSylowIn 2 (T ⊓ Subgroup.normalizer (U : Set G)) (M ⊓ Subgroup.normalizer (U : Set G)) →
      (IsSylowIn 2 (ch6Q T V ⊔ Subgroup.zpowers t) (Subgroup.centralizer (U : Set G)) ∧
        Subgroup.normalizer (thompsonJ (ch6Q T V ⊔ Subgroup.zpowers t) : Set G) ≤ M ∧
        IsSylowIn 2 (T ⊓ Subgroup.normalizer (U : Set G)) (Subgroup.normalizer (U : Set G))) ∧
      (QuasithinUnique.CharTwo (Subgroup.normalizer (U : Set G)) ∧
        QuasithinUnique.CharTwo (Subgroup.centralizer (U : Set G))) ∧
      (wClos V 0 (ch6Q T V ⊔ Subgroup.zpowers t) ≤ ch6Q T V ∧
        (2 < n → wClos V 1 (ch6Q T V ⊔ Subgroup.zpowers t) ≤ ch6Q T V)) ∧
      (IsElemAbelian 2 (conjClosure V (Subgroup.normalizer (U : Set G))) ∧
        IsReducedMod (Subgroup.normalizer (U : Set G))
          (conjClosure V (Subgroup.normalizer (U : Set G))) U ∧
        ⁅pCoreOf 2 (Subgroup.normalizer (U : Set G)),
          conjClosure V (Subgroup.normalizer (U : Set G))⁆ ≤ U) ∧
      (2 < n → ∀ g : G, conjSubgroup V g ≤ Subgroup.centralizer (U : Set G) →
        V ≤ Subgroup.normalizer (conjSubgroup V g : Set G) → ⁅V, conjSubgroup V g⁆ ≠ ⊥ →
        ¬ Subgroup.centralizer (ch6ZS T L V : Set G) ≤ M)

@[expose] def Stmt6_1_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp611Nat G T M L V n →
    ¬ Subgroup.centralizer (ch6ZS T L V : Set G) ≤ M ∨
      (n = 2 ∧ (¬ Subgroup.normalizer (wClos V 0 T : Set G) ≤ M ∨
        ¬ wClos V 1 T ≤ ch6S T L V))

structure Hyp6116 (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ) : Prop
    extends Hyp611Nat G T M L V n where
  not_le : ¬ Subgroup.centralizer (ch6ZS T L V : Set G) ≤ M

@[expose] def IsInHS (T M L V H : Subgroup G) : Prop :=
  InH T H ∧ ¬ H ≤ M ∧ oTwoUpper H ≤ Subgroup.centralizer (ch6ZS T L V : Set G)

@[expose] def Stmt6_1_19 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp6116 G T M L V n →
    (∃ H : Subgroup G, IsInHS T M L V H ∧ IsHStar T M H ∧
      Odd (CosetGeom.critDist (L ⊔ T ⊔ H) (L ⊔ T) H V)) →
    n = 2 ∧ ¬ IsMulCommutative ↥(conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)))

@[expose] def Stmt6_1_25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp6116 G T M L V n →
    ∀ l ∈ L, l ∉ Subgroup.normalizer (ch6ZS T L V : Set G) →
      let I := Subgroup.centralizer (ch6ZS T L V : Set G)
      let H := Subgroup.normalizer (ch6ZS T L V : Set G)
      let U := conjClosure V I
      let R := pCoreOf 2 (U ⊔ conjSubgroup U l)
      let E := U ⊓ conjSubgroup U l
      n = 2 ∧
      (∀ K : Subgroup G, quasithinIsCComponent K I → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
        ¬ ⁅K, R⁆ ≤ centralizerMod (ch6ZS T L V) H U →
        ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
          ∀ _ : ((centralizerMod (ch6ZS T L V) K U).subgroupOf K).Normal,
            LieModel (↥K ⧸ (centralizerMod (ch6ZS T L V) K U).subgroupOf K) .PSL 2 p 1) ∧
      E.relIndex R = 2 ^ n * 2 ^ n

@[expose] def Stmt6_1_26 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp6116 G T M L V n →
    ∀ l ∈ L, l ∉ Subgroup.normalizer (ch6ZS T L V : Set G) →
      let U := conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))
      let R := pCoreOf 2 (U ⊔ conjSubgroup U l)
      let E := U ⊓ conjSubgroup U l
      ∀ e ∈ E, e ∉ V →
        (∀ v ∈ V, ∃ r ∈ R, r * e * r⁻¹ = e * v) ∧ V.relIndex E ≤ 4

@[expose] def Stmt6_1_27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp611 G T M L V n →
    n = 2 ∧
    (IsNatModCh5 L ⁅V, L⁆ 2 ∧ T ⊓ Subgroup.centralizer (L : Set G) = ⊥) ∧
    Subgroup.centralizer (ch6ZS T L ⁅V, L⁆ : Set G) ≤ M ∧
    (¬ Subgroup.normalizer (wClos ⁅V, L⁆ 0 T : Set G) ≤ M ∨
      ¬ wClos ⁅V, L⁆ 1 T ≤ ch6S T L ⁅V, L⁆)

end CFSG.Quasithin.H13
