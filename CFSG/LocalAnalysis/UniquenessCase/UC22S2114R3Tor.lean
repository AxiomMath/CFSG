module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SylowCentralOuter
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3UBorel
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3A
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
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Milestones.ASVolI.I2
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
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
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3B

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114r3u_not_dvd_card_outer_u7 {M L : Subgroup G} (hL : L ∈ calC M) {f r : ℕ}
    (hX : LieModel (BarInf L) .PSU 7 2 f) (hr : r.Prime) (hr5 : 5 ≤ r) (hrf : ¬ r ∣ f) :
    ¬ r ∣ Nat.card (Outer (Bar2 L)) := by
  classical
  have : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr hL.2.2.1
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hdvd : Nat.card (Outer (Bar2 L)) ∣ Nat.card (Outer (BarInf L)) := by
    rw [Nat.card_congr (equivalence e).toEquiv,
      Nat.card_congr (MonoidHom.ofInjective (centerQuotient_outer_injective (Bar2 L))).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hb := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (T := BarInf L) (Or.inr rfl) (by norm_num) Nat.prime_two (LieModel.admissible hX).2.1
    (LieModel.statedClassicalModel hX (by decide))).1
  exact fun h => uc22s2114r3u_not_dvd_out_bound (Or.inr rfl) hr hr5 hrf (h.trans (hdvd.trans hb))

theorem uc22s2114r3_strongly_of_centralizer {D : Data G} (hSg : UC6S846.SigmaStd D)
    (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hML : D.M ≤ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hab : ∀ P : Sylow r (Bar2 L), IsMulCommutative (P : Subgroup (Bar2 L)))
    (hout : ¬ r ∣ Nat.card (Outer (Bar2 L))) {p : ℕ} (hp : p ∈ D.sig) {E : Subgroup G}
    (hEL : E ≤ L) (hEel : IsElemAbelian r E) (hEc : Nat.card E = r ^ 2)
    (hF : 2 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (E : Set G))) :
    IsStronglyPEmbedded r D.M := by
  have : Fact r.Prime := ⟨hr⟩
  have hLM : L ≤ D.M := hL.1.le
  obtain ⟨R, hR, hER⟩ := PartTwo.exists_sylow_le_centralizer_of_isMulCommutative hr hr2 hLM hML
    hab (fun h => hout (h.trans (PartTwo.relIndex_centOverO2_dvd_card_outer hLM hML))) hEL
    hEel.isPGroup
  exact uc22s2114_strongly_of_two_le_pRank_centralizer hSg (UC6S846.not_solvable_of_mem_calC hL)
    h76 h614 hp hr hr2 hR hEel hEc hER hF

theorem uc22s2114r3_false_of_centralizer {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrn : r ∣ 2 ^ c.n - 1) (hZ : ¬ r ∣ Nat.card (center (Bar2 L)))
    (hab : ∀ P : Sylow r (Bar2 L), IsMulCommutative (P : Subgroup (Bar2 L)))
    (hout : ¬ r ∣ Nat.card (Outer (Bar2 L))) {p : ℕ} (hp : p ∈ D.sig) {E : Subgroup G}
    (hEL : E ≤ L) (hEel : IsElemAbelian r E) (hEc : Nat.card E = r ^ 2)
    (hF : 2 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (E : Set G))) : False := by
  have hrσ := uc22s2114_not_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hH c hr hrn
  have hML : D.M ≤ normalizer (L : Set G) := by
    by_contra hnN
    have h4 := UC6S846.calCRankTwice D.M L hL hnN r hr hr2 hZ E hEL hEel 2 hEc
    exact hrσ (hSg.four_mem r hr hr2 (by omega))
  exact uc22s217u3a_false_of_sp D Ch hH c hr hrn
    (uc22s2114r3_strongly_of_centralizer hSg h76 h614 hL hML hr hr2 hab hout hp hEL hEel hEc hF)

end CFSG.LocalAnalysis.UniquenessCase.UC22
