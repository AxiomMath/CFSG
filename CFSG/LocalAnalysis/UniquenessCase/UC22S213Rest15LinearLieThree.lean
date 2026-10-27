module

public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThreeDef
public import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
import CFSG.LocalAnalysis.StandardType.GGSpNbrKGInj
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

set_option linter.unusedVariables false in
theorem rest15_false_of_linear_lie_three
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M)
    {L X H K P : Subgroup G} (hL : L ∈ calC S.M)
    (hLN : S.M ≤ normalizer (L : Set G)) (hthin : ¬ F08.Thin8 L)
    (hXL : X ≤ L) (hsupp : X ⊔ pCoreOf 2 L = L)
    (hHtop : H ≠ ⊤) (hHr : CFSG.Open.pRank 3 H ≤ 3)
    (hnotStrong : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    (hXcomp : CFSG.Open.IsComponentOf X (H ⊓ S.M))
    (hKcomp : CFSG.Open.IsComponentOf K H) (hXK : X ≤ K) (hKM : ¬ K ≤ S.M)
    (hX : CFSG.Blueprint.LieModel X .PSL 3 2 2)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P X)
    (hGamma : rankThreeGamma 1 3 P ≤ S.M)
    (hNormal : (X.subgroupOf (H ⊓ S.M)).Normal)
    (hGammaH : rankThreeGamma 1 3 (P.subgroupOf H) ≤
      (normalizer (X : Set G)).subgroupOf H)
    (hZK : ¬ 3 ∣ Nat.card (center K))
    (hAlt : ¬ ∃ n : ℕ, 5 ≤ n ∧
      Nonempty (K ⧸ center K ≃* alternatingGroup (Fin n)))
    {d : TauCeti.ValidLieTypeIndex} (hchar : 3 = d.1.characteristic)
    (e : K ⧸ center K ≃* (TauCeti.CFSGIndex.lie d).Group) : False := by
  clear hS hU hMS hPart hL hLN hthin hXL hsupp hHtop hnotStrong hKM hP hGamma hNormal hGammaH hAlt
  have hKrank : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hKcomp.1).trans hHr
  have hQrank : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ center K)) ≤ 3 := by
    rw [CFSG.SectionRank.pRank_quotient_eq (center K) hZK]
    exact hKrank
  have hZX : center X = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.center_eq_bot_of_simple
      (hX.isSimpleGroup_of_mem_classicalTags (by simp [CFSG.Blueprint.classicalTags]))
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.exists_noncomm_of_quasisimple
        hXcomp.2.2)
  obtain ⟨ι, hι, -⟩ := CFSG.StandardType.exists_inj_hom_centerQuot
    (MulEquiv.refl (K ⧸ center K)) X.subtype X.subtype_injective (Subgroup.range_subtype X) hXK hZX
  have hdiv : 20160 ∣ Nat.card (K ⧸ center K) := by
    rw [← CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four
      (hX.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags]))]
    exact Subgroup.card_dvd_of_injective ι hι
  rcases CFSG.LocalAnalysis.AGL81I.Section3.lieDefThree_rank_three_cases
      CFSG.LieType.defCharRankFourExc CFSG.TauCetiBridge.chevalleyBridges.g2 hchar e hQrank with
    hL29 | hL227 | hL33 | hU33 | hS43
  · rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_nine hL29] at hdiv
    norm_num at hdiv
  · rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) hL227] at hdiv
    norm_num at hdiv
  · obtain ⟨φ⟩ := hL33
    rw [Nat.card_congr φ.toEquiv,
      CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear (ZMod 3) 3 (by norm_num),
      Nat.card_zmod] at hdiv
    norm_num [Finset.prod_Icc_succ_top (by norm_num : 2 ≤ (3 : ℕ))] at hdiv
  · rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hU33] at hdiv
    norm_num at hdiv
  · rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hS43] at hdiv
    norm_num [CFSG.EvenSmallLie.CatalogOrders.lieOrd, CFSG.Open.ordBC,
      Finset.prod_Icc_succ_top (by norm_num : 1 ≤ (2 : ℕ))] at hdiv

end CFSG.LocalAnalysis.UniquenessCase.UC22
