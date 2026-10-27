module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToral
public import CFSG.LieType.AlgebraicGroups.ToralRootCover
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
public import CFSG.Assembly.Subnormal
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.WeylCharStab
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Timmesfeld.CrossChar

private theorem ggTBJ_exists_unit_sq_ne_one_aux {K : Type} [Field K] [Finite K]
    (hK : 4 ≤ Nat.card K) : ∃ t : Kˣ, t ^ 2 ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have h1 : Nat.card (rootsOfUnity 2 K) ≤ 2 := card_rootsOfUnity K 2
  have h2 : Nat.card Kˣ ≤ Nat.card (rootsOfUnity 2 K) :=
    Nat.card_le_card_of_injective (fun t => ⟨t, (mem_rootsOfUnity 2 t).2 (hcon t)⟩)
      fun s t h => congrArg Subtype.val h
  have h3 : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  omega

private theorem ggTBJ_torusGroup_mul_comm_aux
    {τ : Tag} {K : Type} [Field K] {x y : ModGL τ K}
    (hx : x ∈ torusGroup τ K) (hy : y ∈ torusGroup τ K) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

private theorem ggTBJ_isSolvable_sup_quotient_aux {G : Type*} [Group G] {H N : Subgroup G}
    [(N.subgroupOf (H ⊔ N)).Normal] (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hLE : H ≤ Subgroup.normalizer (N : Set G)) :
    Group.IsSolvable (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) := by
  haveI : (N.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLE
  haveI : Group.IsSolvable ↥H := Group.isSolvable_of_comm fun x y => Subtype.ext (hH x x.2 y y.2)
  let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hLE
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

theorem ggTBJ_perfect_le_rootSpan
    (τ : Tag) {K : Type} [Field K] [Finite K]
    (hK : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (a : Fin τ.rank → Kˣ) (ha : ∀ i, a i ^ p = 1)
    (P : Subgroup (ModGL τ K)) (hP : P ≤ toralCentralizer τ K a) (hperf : ⁅P, P⁆ = P) :
    P ≤ rootSpan τ K (rootCharKernel a) := by
  obtain ⟨hMX, hMn, -, -, φ, hφ, -⟩ := Chevalley_toral_centralizer_root_generated_quotient τ K a
  haveI : ((toralRootGroup τ K a).subgroupOf (toralCentralizer τ K a)).Normal := hMn
  have hCN : Group.IsSolvable (↥(toralCentralizer τ K a) ⧸
      (toralRootGroup τ K a).subgroupOf (toralCentralizer τ K a)) := by
    haveI := isSolvable_quotient hp ha
    exact Group.isSolvable_of_surjective hφ
  have hPM : P ≤ toralRootGroup τ K a :=
    perfect_le_of_solvable_quotient hMX hCN hP hperf
  have hTU : torusGroup τ K ≤
      Subgroup.normalizer (rootSpan τ K (rootCharKernel a) : Set (ModGL τ K)) :=
    torusGroup_le_normalizer_rootSpan fun _ hα => hα.1
  have hUM : rootSpan τ K (rootCharKernel a) ≤ toralRootGroup τ K a := le_sup_right
  haveI hUn : ((rootSpan τ K (rootCharKernel a)).subgroupOf (toralRootGroup τ K a)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hTU
  have hMU : Group.IsSolvable (↥(toralRootGroup τ K a) ⧸
      (rootSpan τ K (rootCharKernel a)).subgroupOf (toralRootGroup τ K a)) := by
    haveI : ((rootSpan τ K (rootCharKernel a)).subgroupOf
        (torusGroup τ K ⊔ rootSpan τ K (rootCharKernel a))).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hTU
    exact ggTBJ_isSolvable_sup_quotient_aux
      (fun _ hx _ hy => ggTBJ_torusGroup_mul_comm_aux hx hy) hTU
  exact perfect_le_of_solvable_quotient hUM hMU hPM hperf

theorem ggTBJ_isComponentOf_componentRootSpan
    (τ : Tag) {K : Type} [Field K] [Finite K]
    (hK : 4 ≤ Nat.card K) (a : Fin τ.rank → Kˣ) (i : KernelComponent (rootCharHom a)) :
    IsComponentOf (componentRootSpan K (rootCharHom a) i) (toralCentralizer τ K a) := by
  obtain ⟨t, ht⟩ := ggTBJ_exists_unit_sq_ne_one_aux hK
  exact ⟨componentRootSpan_le_toralCentralizer a i,
    (CFSG.Open.IsSubnormal.iff_subgroupOf (componentRootSpan_le_toralCentralizer a i)).2
      (isSubnormal_componentRootSpan a i),
    open_isQuasisimple (isQuasisimple_componentRootSpan_of_sq_ne_one ht i)⟩

end CFSG.StandardType

end
