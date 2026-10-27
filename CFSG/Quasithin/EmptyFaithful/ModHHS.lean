module

public import CFSG.Quasithin.EmptyFaithful.ModHNS
public import CFSG.Quasithin.EmptyFaithful.ModHSolv
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.Sporadic.HS
public import CFSG.GroupTheory.WeirSylow.GL
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1AutModel
public import CFSG.Quasithin.Background.A318PL3Unit
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.FFC4Res
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.ModHEl
public import CFSG.Quasithin.EmptyFaithful.ModHPerm
public import CFSG.Quasithin.EmptyFaithful.R3c11Core
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S153G27
public import CFSG.Quasithin.EmptyFaithful.SBd12Main
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.H13.A5S136b
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
public import CFSG.Sporadic.Schreier.J4SNoCompCover
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Walter.J1Props
public import CFSG.Walter.J1Recog
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.Statements
public import Certificates.Kernel.J4Count.Prim
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.HS

theorem solvNineNS_HS :
    SolvNineNS (NativeSporadic.Carrier .HS) := by
  intro hns P Y hP hN hs h9
  have hfin : Finite (NativeSporadic.Carrier .HS) := (CFSG.Sporadic.HS.fam_hs_simplicity).1
  have hZs := isSolvable_sup_of_le_normalizer hs hP.2.1 hN
  have hPZ : P ≤ Y ⊔ P := le_sup_right
  have h9Z : 9 ∣ Nat.card ↥(Y ⊔ P) := h9.trans (Subgroup.card_dvd_of_le le_sup_left)
  rcases hs_overgroups (X := NativeSporadic.Carrier .HS) ⟨MulEquiv.refl _⟩ hP hPZ with htop | ⟨m, hm, hord, -, -⟩
  · apply hns
    rw [htop] at hZs
    exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup (NativeSporadic.Carrier .HS)).subtype)
      (by intro x; exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
  · rw [hord] at h9Z
    simp only [hsMems, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> exact absurd h9Z (by decide)

end CFSG.Quasithin.ModH
