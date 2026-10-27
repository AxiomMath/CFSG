module

public import CFSG.RankThree.PartOne.S12.Sec1510FiveBundle
public import CFSG.RankThree.PartOne.K1510R.NN
public import CFSG.RankThree.PartOne.K1510R.Core
public import CFSG.RankThree.PartOne.K1510R.Stair
public import CFSG.RankThree.PartOne.K1510R.StairEmpty
import CFSG.RankThree.PartOne.K159G.CompGen

public section

namespace CFSG.RankThree.PartOne.K1510R

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem kf1510Reg_of_inputs
    (h154 : Node154) (h155 : Node155) (h158 : Node158) (h158E3 : S15K.Node158E3)
    (h159 : Node159Five) (hR : U5E.Reinst5) (hInn : KFInnLayerFive) (hKE : KF1510E)
    (hMod : KFU5Mod) (hAt : KFU5At) (hSLB : N143.SectionListBound) (hZ : KF159ZFiveGen)
    (hExt : N143.ExtFiveList) (hEin : U5K.U5EInndiag) (hPerf : K159.KFPerfNormalizerFive)
    (hLR5 : S15K.LayerRowFive) (hGen : K159.KFCompGenFive) : KF1510Reg := by
  intro G _ _ p A c L E h15 hF hout e heE he1 _
  have hNn : ∀ B : Subgroup G, B ≤ E → ¬ IsCyclic ↥B →
      Subgroup.normalizer (B : Set G) ≤ lieNormalizer p E := fun B hBE hB =>
    normalizer_le_of_noncyclic h154 h155 h158 h158E3 h159 hR hInn hKE hMod hAt h15 hF hout hBE hB
  have hLN : ∀ Z ∈ thetaComponentsAt p e, Z ≤ lieNormalizer p E := fun Z hZ' =>
    core_reg h154 h155 h158E3 hSLB hZ hExt h15 hF hout hNn heE he1 hZ'
  by_cases hcen : CentralizesE p E e
  · exact cent_le_of_LN h155 h158 h158E3 hR hInn hKE h15 hF hout heE he1 hcen hLN
  · have hp := h15.h12.prime
    have hp5 : p = 5 := by
      by_contra hne
      have h5 : 5 ≤ p := by
        have h3 := h15.h12.three_lt
        by_contra hlt
        have h4 : p = 4 := by omega
        exact absurd (h4 ▸ hp) (by norm_num)
      have h6 : p ≠ 6 := fun h6 => by rw [h6] at hp; norm_num at hp
      have hp7 : 7 ≤ p := by omega
      exact hcen (centralizesE_of_seven hp hp7 h15 hF h154 hout e)
    obtain ⟨M⟩ := Sec153.nonempty_modData hMod h15 hF hout
    subst hp5
    have hN : ∀ t ∈ reflectionSet 5 E, e ∉ autFixedInG E t := fun t ht het =>
      hcen (centralizesE_of_mem_autFixedInG_five h15.h12 M ht het he1)
    exact stair_of_empty rfl h155 h15 hF hout M hNn heE
      (thetaComponentsAt_empty hEin hPerf hLR5 hGen hAt h15 hF hout heE he1 hN hLN)

theorem node1510Five_of_bundleGen
    (hS : SchreierFor InCatalog) (hSC : SchreierFor CFSG.Blueprint.Catalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) (hbridge : TauCetiCatalogBridge)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSLB : N143.SectionListBound) (hSeitz : CTP.SeitzResidual)
    (hMod : KFU5Mod) (hAt : KFU5At) (hFive : U5FiveInndiag)
    (h154 : Node154) (h155 : Node155) (h158 : Node158) (h158E3 : S15K.Node158E3) (h156 : KF156')
    (hR : U5E.Reinst5) (hZresGen : KF159ZFiveResGen) : Node1510Five := by
  obtain ⟨h159, hInn, hE⟩ := node1510Five_inputs_of_bundle hS hSC h82 hbridge hGA hSLB hSeitz hMod
    hAt hFive h154 h155 h158 h158E3 h156 hR (kf159ZFiveRes_of_gen hZresGen)
  have hEin : U5K.U5EInndiag := U5K.u5EInndiag_of hMod hAt hFive
  have hPerf : K159.KFPerfNormalizerFive := K159.kfPerfNormalizerFive_of_schreier hSC hMod hAt hFive
  have hLR5 : S15K.LayerRowFive := S15K.layerRowFive_of_package hMod hAt hFive
  have hGen : K159.KFCompGenFive := K159.kfCompGenFive_of hAt hEin
  have hZ : KF159ZFiveGen :=
    kf159ZFiveGen_of_inputs h155 (K159F.centerRankFive_of_griess hbridge hGA) hZresGen
  have hExt : N143.ExtFiveList := N143.extFiveList_of_inputs_seitzThree
      (CTP.extSeitzThree_of_residual hSeitz) CTP.charPNoncommInput
      (K159F.sporadicFiveInput_of_leTwo SPOR.sporadicOuterOrderLeTwoSimple_holds)
  exact node1510Five_of_reg_core h155 h158 h158E3 h159 hR hInn hE
    (kf1510Reg_of_inputs h154 h155 h158 h158E3 h159 hR hInn hE hMod hAt hSLB hZ hExt hEin hPerf hLR5
      hGen)

end CFSG.RankThree.PartOne.K1510R
