module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Spec
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsLie
public import CFSG.Quasithin.Recognition.RuTypeTwoF4M
public import CFSG.Quasithin.Recognition.RuTypeJ47k
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.Statements
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S1421Final
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.Recognition.RuTypeJ36f
public import CFSG.Quasithin.Recognition.RuTypeJ45a
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuType.J47 CFSG.Quasithin.H13.F45Ru
  CFSG.Sporadic.Schreier.Tits CFSG.RuF45 CFSG.TwoF4Lie CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

set_option linter.unusedSectionVars false

theorem mem_twoF4M_of_mem_A {x : Equiv.Perm (Fin 1755)} (hx : x ∈ TA) : x ∈ twoF4M := by
  rw [twoF4M_eq_titsA]
  exact hx

theorem twoF4S_le_twoF4M : twoF4S ≤ twoF4M := twoF4S_le_twoF4H.trans twoF4H_le_twoF4M

@[expose] noncomputable def zM : ↥twoF4M := ⟨titsZ, mem_twoF4M_of_mem_A titsZ_mem_A⟩

@[expose] noncomputable def tM : ↥twoF4M := ⟨tEl.1, mem_twoF4M_of_mem_A tEl.2⟩

@[expose] noncomputable def twoF4TT : Subgroup ↥twoF4M := twoF4S.subgroupOf twoF4M

@[expose] noncomputable def twoF4M1 : Subgroup ↥twoF4M := twoF4H.subgroupOf twoF4M

@[expose] noncomputable def twoF4M2 : Subgroup ↥twoF4M := twoF4N.subgroupOf twoF4M

theorem invStep_of_step {x y : Equiv.Perm (Fin 1755)} (h : Certificates.c4180Step x y)
    (hx : x ∈ twoF4M) (hy : y ∈ twoF4M) : InvStep twoF4TT twoF4M1 twoF4M2 ⟨x, hx⟩ ⟨y, hy⟩ := by
  obtain ⟨⟨hxA, hx0, hxL⟩, ⟨hyA, hy0, hyL⟩, g, hgA, hg, rfl⟩ := h
  refine ⟨(Subgroup.mem_subgroupOf).2 ((mem_twoF4S_iff hxA).2 ⟨hx0, hxL⟩),
    (Subgroup.mem_subgroupOf).2 ((mem_twoF4S_iff hyA).2 ⟨hy0, hyL⟩),
    ⟨g, mem_twoF4M_of_mem_A hgA⟩, ?_, Subtype.ext rfl⟩
  rcases hg with h | h
  · exact Or.inl ((Subgroup.mem_subgroupOf).2 ((mem_twoF4H_iff hgA).2 h))
  · exact Or.inr ((Subgroup.mem_subgroupOf).2 ((mem_twoF4N_iff hgA).2 h))

theorem chain_of_steps {a b : Equiv.Perm (Fin 1755)}
    (h : Relation.ReflTransGen Certificates.c4180Step a b) (ha : a ∈ twoF4M) :
    ∀ hb : b ∈ twoF4M,
      Relation.ReflTransGen (InvStep twoF4TT twoF4M1 twoF4M2) ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | refl => exact fun _ => Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    intro hc
    exact (ih (mem_twoF4M_of_mem_A hbc.1.1)).tail (invStep_of_step hbc _ hc)

theorem inv_chain_model : ∀ i ∈ twoF4TT, orderOf i = 2 →
    Relation.ReflTransGen (InvStep twoF4TT twoF4M1 twoF4M2) zM i ∨
      Relation.ReflTransGen (InvStep twoF4TT twoF4M1 twoF4M2) tM i := by
  obtain ⟨-, -, -, hch⟩ := Certificates.certificate4180
  intro i hi ho
  have h2 : i * i = 1 := by
    rw [← pow_two]
    exact ho ▸ pow_orderOf_eq_one i
  have h1 : i ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ho
    omega
  have hiA : i.1 ∈ TA := by
    rw [← twoF4M_eq_titsA]
    exact i.2
  obtain ⟨hi0, hiL⟩ := (mem_twoF4S_iff hiA).1 (Subgroup.mem_subgroupOf.1 hi)
  have htM : tM = ⟨Certificates.c4180T, by rw [← tEl_eq]; exact tM.2⟩ := Subtype.ext tEl_eq
  rcases hch i.1 hiA hi0 hiL (congrArg Subtype.val h2) (fun h => h1 (Subtype.ext h)) with h | h
  · exact Or.inl (chain_of_steps h zM.2 i.2)
  · rw [htM]
    exact Or.inr (chain_of_steps h _ i.2)

end CFSG.Quasithin.H13.F431.TwoF4
