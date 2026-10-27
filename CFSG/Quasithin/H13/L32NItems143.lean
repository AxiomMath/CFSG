module

public import CFSG.Quasithin.H13.L32NNotation
public import CFSG.Quasithin.H13.StatementsL2
public import CFSG.Quasithin.H13.StatementsVocab
public import CFSG.Quasithin.Recognition.RuTypeDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Foundations
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.H13.L32NStatements
public import CFSG.Quasithin.Recognition.G23TypeDefs
public import CFSG.Quasithin.Recognition.HSTypeDefs
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def StmtL32NModule : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp14_3_1One G T L → FSU G T L V →
    IsElemAbelian 2 V ∧ Nat.card V = 8 ∧ L ⊔ T ≤ Subgroup.normalizer (V : Set G) ∧
      Nat.card ↥(fsuV1 T V) = 2 ∧
      ∃ _ : IsMulCommutative ↥V, BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 3 1

@[expose] def Lemma1433Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp14_3_1One G T L → FSU G T L V →
    Subgroup.normalizer (V : Set G) =
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)

@[expose] def Lemma14323Ge : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp14310One G T L V →
    2 ^ 4 * Nat.card ↥(centerOf (fsuU T V)) ≤ Nat.card ↥(fsuU T V)

structure Concl14332 (T V : Subgroup G) : Prop where
  sym : ∃ φ : ↥(l32nH T V) →* Equiv.Perm (Fin 5), Function.Surjective φ ∧
    φ.ker = (l32nCHat T V).subgroupOf (l32nH T V)
  natural : ∃ (φ : ↥(l32nH T V) →* RuType.SigmaL2F4)
      (ψ : ↥(fsuU T V) →* Multiplicative (Fin 2 → RuType.F4)),
    Function.Surjective φ ∧ φ.ker = (l32nCHat T V).subgroupOf (l32nH T V) ∧
    Function.Surjective ψ ∧ ψ.ker = (centerOf (fsuU T V)).subgroupOf (fsuU T V) ∧
    ∀ (h : ↥(l32nH T V)) (u u' : ↥(fsuU T V)), (u' : G) = h * u * (h : G)⁻¹ →
      ψ u' = Multiplicative.ofAdd (RuType.sigmaAct (φ h) (Multiplicative.toAdd (ψ u)))
  z4q8q8 : HSType.IsZ4Q8Q8 ↥(fsuU T V)
  q_eq : pCoreOf 2 (l32nH T V) = l32nCHat T V
  comp : ∃ K : Subgroup G, quasithinIsCComponent K (l32nH T V) ∧ l32nH T V = K ⊔ T ∧
    fsuU T V = ⁅pCoreOf 2 K, K⁆ ∧ IsIndecOnSection K (fsuU T V) (fsuV1 T V)

@[expose] def Lemma14332 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp14310One G T L V →
    fsuV1 T V < centerOf (fsuU T V) → Concl14332 T V

structure Concl14333 (T L V : Subgroup G) : Prop where
  p_eq : pCoreOf 2 L = conjClosure (centerOf (fsuU T V)) L
  p_iso : HSType.IsZ4Cube ↥(pCoreOf 2 L)
  p_mod : IsXSectionIso₂ L (pCoreOf 2 L) V V ⊥
  u_eq : fsuU T V = pCoreOf 2 (oTwoUpper (l32nH T V))
  sylow : QuasithinUnique.IsSylowTwoOf (pCoreOf 2 L ⊔ fsuU T V) (oTwoUpper (l32nH T V))
  m_eq : Subgroup.normalizer (L : Set G) = L
  h_eq : l32nH T V = oTwoUpper (l32nH T V) ⊔ T
  u_eq_q : fsuU T V = pCoreOf 2 (l32nH T V)

@[expose] def Lemma14333 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp14310One G T L V →
    fsuV1 T V < centerOf (fsuU T V) → Concl14333 T L V

end CFSG.Quasithin.H13
