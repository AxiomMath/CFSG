module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bridge
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.CharacterTheory.CyclicBlocks.Family
import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
import CFSG.ClassicalGroups
import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.Combinatorics.AperiodicCentralInvolution
import CFSG.Combinatorics.AperiodicFiveOfSix
import CFSG.Combinatorics.AperiodicOppositeComponents
import CFSG.Combinatorics.AperiodicSixteenGraphDistances
import CFSG.Combinatorics.OuterLayerPredecessors
import CFSG.GH74.GLS.IVK.L2.F1
import CFSG.GH74.KGroups.L3EpsNoNormalThree
import CFSG.GH74.KGroups.L3EpsOutExp
import CFSG.GH74.KGroups.L3EpsOuterLin
import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
import CFSG.LieType.SeitzGeneration.UnitaryBlocks
import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
import CFSG.LocalAnalysis.SectionRank.QTK.Exc
import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs
import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
import CFSG.Permutation.UnitaryThreeRecognition.Model
import CFSG.Quasithin.Background.RonanE111Defs
import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
import CFSG.RankThree.OddKernel.CompleteRankComparison
import CFSG.RankThree.PartOne.KF.ClsPSL
import CFSG.RankThree.PartOne.KF.SU5Model
import CFSG.RankThree.PartOne.KF.SymCtxMatrix
import CFSG.RankThree.PartOne.KF.ToralQuot
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.RankThree.PartOne.S11c.Sec66PSL
import CFSG.RankThree.PartOne.S11c.Sec66Sp
import CFSG.RankThree.PartOne.S11c.SuFiveD
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  (InFGroup IsOmegaColl genEi InCalEi ECaseI ECaseII normAIn)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (IsEP eGenP ETwoPrint)
open scoped Pointwise

private theorem isInvColl_top_of_isOmegaColl {G : Type} [Group G] {Ω : Set (Subgroup G)}
    (h : IsOmegaColl Ω) : E1.IsInvColl (⊤ : Subgroup G) Ω where
  le _ _ := le_top
  isElemAbelian := h.elemAbelian
  conj A hA t _ := by
    have h1 := h.conj A hA t⁻¹
    rwa [conjSubgroup_eq_conjSub, inv_inv] at h1

private theorem eCaseI_of_eOne {G : Type} [Group G] [Finite G] {A K : Subgroup G}
    (hAK : A ≤ K) (h : E1.EOne ↥K (A.subgroupOf K)) : ECaseI A K := by
  obtain ⟨p, hp, hp2, hoTwo, -, hcomm, hcard⟩ := h
  refine ⟨p, hp, hp2, hoTwo, ?_, (card_barO2_subgroupOf_eq hAK).symm.trans hcard⟩
  rw [fittingSubgroup_bar2_eq_pCore hp hp2 hoTwo, Subgroup.commutator_comm]
  exact hcomm

private theorem eCaseII_of_eTwoPrint {G : Type} [Group G] [Finite G] {T A K : Subgroup G}
    (hAK : A ≤ K) (hA : IsPGroup 2 A)
    (h : ETwoPrint ↥K ((E1.tauOf (⊤ : Subgroup G) T A).subgroupOf K) (A.subgroupOf K)) :
    ECaseII T A K := by
  obtain ⟨h2c, hpCore, hres, L, hL, hlayer, haltern⟩ := h
  refine ⟨h2c, hpCore, hres, L, hL, hlayer, ?_⟩
  rcases haltern with hI | ⟨hnot, hcard⟩
  · exact Or.inl hI
  right
  have : Fact (Nat.card ↥(E1.barRad ↥K (A.subgroupOf K))).Prime := ⟨hcard ▸ Nat.prime_two⟩
  have hbot : (normalizer (L : Set (↥K ⧸ CFSG.solvableRadical ↥K))).subgroupOf
      (E1.barRad ↥K (A.subgroupOf K)) = ⊥ :=
    (Subgroup.eq_bot_or_eq_top_of_prime_card _).resolve_right fun htop =>
      hnot (Subgroup.subgroupOf_eq_top.mp htop)
  have hN : normAIn A K L = A ⊓ (CFSG.solvableRadical ↥K).map K.subtype := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, ⟨hxA, hxN⟩, rfl⟩
      refine ⟨hxA, x, ?_, rfl⟩
      have hmem : (⟨QuotientGroup.mk' (CFSG.solvableRadical ↥K) x, x, hxA, rfl⟩ :
          ↥(E1.barRad ↥K (A.subgroupOf K))) ∈
          (normalizer (L : Set (↥K ⧸ CFSG.solvableRadical ↥K))).subgroupOf
            (E1.barRad ↥K (A.subgroupOf K)) := hxN
      rw [hbot, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff x).mp (congrArg Subtype.val hmem)
    · rintro _ ⟨hyA, x, hxR, rfl⟩
      refine ⟨x, ⟨hyA, ?_⟩, rfl⟩
      have h1 : QuotientGroup.mk' (CFSG.solvableRadical ↥K) x = 1 :=
        (QuotientGroup.eq_one_iff x).mpr hxR
      show QuotientGroup.mk' (CFSG.solvableRadical ↥K) x ∈
        normalizer (L : Set (↥K ⧸ CFSG.solvableRadical ↥K))
      rw [h1]
      exact Subgroup.one_mem _
  refine ⟨?_, hN.trans (inf_solvableRadical_eq_inf_pCoreOf hAK hA h2c)⟩
  rw [hN, Subgroup.inf_relIndex_left, ← card_barRad_subgroupOf_eq hAK]
  exact hcard

private theorem inCalEi_of_isEP {G : Type} [Group G] [Finite G] {i : ℕ} {T A K : Subgroup G}
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (h : IsEP i (⊤ : Subgroup G) T A K) :
    InCalEi i T A K := by
  obtain ⟨-, hτ, hsyl, hcase⟩ := h
  have hA2 : IsPGroup 2 A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g g.2)⟩
  have hAK : A ≤ K := (le_tA_of_isElemAbelian hAT hA).trans (hτ.trans inf_le_right)
  have hsylOf : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K) K :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr hsyl
  have hm : (pCoreOf 2 K).relIndex A ≤ 2 ^ i → E3.mQuot A (pCoreOf 2 K) ≤ i := fun hle => by
    rw [E3.relIndex_eq_two_pow hA2] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  rcases hcase with ⟨hE1, hcard⟩ | ⟨hE2, hcard⟩
  · have hI := eCaseI_of_eOne hAK hE1
    refine ⟨⟨hτ, hsylOf, fun hle => ?_, Or.inl hI⟩,
      hm ((card_barO2_subgroupOf_eq hAK).symm.trans_le hcard)⟩
    obtain ⟨-, -, -, -, -, hrel⟩ := hI
    rw [Subgroup.relIndex_eq_one.mpr hle] at hrel
    omega
  · have h2 : ((CFSG.solvableRadical ↥K).map K.subtype).relIndex A =
        (pCoreOf 2 K).relIndex A := by
      rw [← Subgroup.inf_relIndex_right, inf_comm,
        inf_solvableRadical_eq_inf_pCoreOf hAK hA2 hE2.1, inf_comm, Subgroup.inf_relIndex_right]
    refine ⟨⟨hτ, hsylOf, fun hle => ?_, Or.inr (eCaseII_of_eTwoPrint hAK hA2 hE2)⟩,
      hm (h2 ▸ (card_barRad_subgroupOf_eq hAK) ▸ hcard)⟩
    have hbar : E1.barRad ↥K (A.subgroupOf K) = ⊥ := by
      refine Subgroup.card_eq_one.mp ?_
      rw [card_barRad_subgroupOf_eq hAK, h2]
      exact Subgroup.relIndex_eq_one.mpr hle
    obtain ⟨-, -, -, L, hL, -, halt⟩ := hE2
    rcases halt with hLb | ⟨hnot, -⟩
    · rw [hbar, Subgroup.commutator_bot_right] at hLb
      have : Subsingleton ↥L := by rw [hLb]; infer_instance
      obtain ⟨-, -, a, b, hab⟩ := hL.1
      exact hab (Subsingleton.elim (a * b) (b * a))
    · exact hnot (hbar ▸ bot_le)

private theorem eGenP_le_genEi {G : Type} [Group G] [Finite G] (i : ℕ) (T : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsOmegaColl Ω) :
    eGenP i (⊤ : Subgroup G) T Ω ≤ genEi i T Ω := by
  unfold genEi eGenP
  refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
  have hK' : InCalEi i T A K := inCalEi_of_isEP hAT (hΩ.elemAbelian A hA) hK
  exact le_iSup₂_of_le A hA (le_iSup_of_le hAT (le_iSup₂_of_le K hK' le_rfl))

theorem inFGroup_of_inF_top (j : ℕ) {Q : Type} [Group Q] [Finite Q]
    (h : UC22.F12.InF j (⊤ : Subgroup Q)) : PartTwo.InFGroup j Q := by
  intro T hT Ω hΩ
  have hprod : ((eGenP j (⊤ : Subgroup Q) T Ω : Subgroup Q) : Set Q) * (T : Set Q) =
      ((⊤ : Subgroup Q) : Set Q) :=
    h T hT Ω (isInvColl_top_of_isOmegaColl hΩ) hΩ.nonempty hΩ.ne_bot
  have hle := eGenP_le_genEi j T hΩ
  rw [Subgroup.coe_top] at hprod
  refine Set.eq_univ_of_univ_subset ?_
  rw [← hprod]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact ⟨x, hle hx, y, hy, rfl⟩

end CFSG.LocalAnalysis.WeakClosure81
