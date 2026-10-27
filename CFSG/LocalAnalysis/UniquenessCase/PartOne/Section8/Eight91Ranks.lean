module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRankBound
public import CFSG.Blueprint.LieModelAPI
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.GroupTheory.CoprimeActionSupport.AbelianEquivalence
public import CFSG.GroupTheory.CoprimeActionSupport.Geometry
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialOrder
public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
public import CFSG.LocalAnalysis.RankThreeUC.WeakModules
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CentralCoverComponentModels
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)

open CFSG.LocalAnalysis.UniquenessCase.PartTwo

private theorem k891ranks_pRank_eq_pRank_bar2 {G : Type} [Group G] [Finite G] (L : Subgroup G)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p L = CFSG.Open.pRank p (⊤ : Subgroup (Bar2 L)) := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hN : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥L) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) hp hp2
  calc CFSG.Open.pRank p L = CFSG.Open.pRank p (⊤ : Subgroup ↥L) :=
        CFSG.SectionRank.pRank_eq_pRank_top_subgroup L
    _ = CFSG.Open.pRank p (⊤ : Subgroup (Bar2 L)) :=
        (CFSG.SectionRank.pRank_quotient_eq (p := p) (G := ↥L) (CFSG.pCore 2 ↥L) hN).symm

private theorem k891ranks_pRank_bar2_le_two {G : Type} [Group G] [Finite G] (D : Data G)
    (hPrime : R891PrimeCore) (L S : Subgroup G) (n : ℕ) (hset : R891Set D L S n)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    CFSG.Open.pRank p (⊤ : Subgroup (Bar2 L)) ≤ 2 :=
  ((hPrime.1 (Bar2 L) n hset.d4).2 p hp hp5).1

private theorem k891ranks_pRank_centOverO2_le_one {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hLM : L ≤ D.M) (hbasic : R891Basic D L S)
    (hctx : R891Ctx D L S n R A) (hcent : R891CentRank D L S A)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : 3 ≠ p) (hpσ : p ∈ D.sig) :
    CFSG.Open.pRank p (CentOverO2 D.M L) ≤ 1 := by
  have hRX : A ⊔ ZOf (S ⊓ L) ≤ L :=
    sup_le hctx.classes.aLe ((inf_le_left : ZOf (S ⊓ L) ≤ S ⊓ L).trans inf_le_right)
  have hRp : IsPGroup 3 ↥(A ⊔ ZOf (S ⊓ L)) :=
    IsPGroup.to_le (p := 3) (hK := hbasic.sylowL.isPGroup)
      (sup_le (hctx.aLeR.trans hctx.xShape.rSylow) (inf_le_left : ZOf (S ⊓ L) ≤ S ⊓ L))
  exact (pRank_centOverO2_le_pRank_inf_centralizer hLM hbasic.normal hp hp2 Nat.prime_three
    (by norm_num) hp3 hRX hRp).trans (hcent p hpσ)

theorem s891_rank {G : Type} [Group G] [Finite G] (D : Data G) (hSg : SigmaStd D) (hOut : R891OutCore) (hPrime : R891PrimeCore)
    (L S R A : Subgroup G) (n : ℕ) (hset : R891Set D L S n) (hbasic : R891Basic D L S) (hctx : R891Ctx D L S n R A)
    (hcent : R891CentRank D L S A) :
    R891Rank893 D L := by
  intro p hpσ
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hset.mem
  have h3not : 3 ∉ D.sig := fun h3 => hset.notStrong (UC6S846.sp_of_mem_sig hSg hns h3)
  have hp3 : 3 ≠ p := fun h => h3not (h ▸ hpσ)
  have hp4 : p ≠ 4 := by
    rintro rfl
    exact (by norm_num : ¬ Nat.Prime 4) hp
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    omega
  have hsp := UC6S846.sp_of_mem_sig hSg hns hpσ
  have hOp : UC22.F10.OpRes p D.M = D.M :=
    UC6.opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab hp hsp
  have hLM : L ≤ D.M := hset.mem.1.le
  have hMbound : CFSG.Open.pRank p D.M ≤
      CFSG.Open.pRank p (⊤ : Subgroup (Bar2 L)) + CFSG.Open.pRank p (CentOverO2 D.M L) :=
    pRank_le_pRank_bar2_add_pRank_centOverO2 hLM hbasic.normal hbasic.centerBot
      (hOut (Bar2 L) n hset.d4).1 hp hp2 hOp
  have hbar : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 L)) ≤ 2 :=
    k891ranks_pRank_bar2_le_two D hPrime L S n hset hp hp5
  have hLbar : CFSG.Open.pRank p L = CFSG.Open.pRank p (⊤ : Subgroup (Bar2 L)) :=
    k891ranks_pRank_eq_pRank_bar2 L hp hp2
  have hcent1 : CFSG.Open.pRank p (CentOverO2 D.M L) ≤ 1 :=
    k891ranks_pRank_centOverO2_le_one D L S R A n hLM hbasic hctx hcent hp hp2 hp3 hpσ
  have hthree := hSg.three_le p hpσ
  constructor
  · rw [hLbar]; omega
  · omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
